{-# LANGUAGE BangPatterns #-}
-- | Lowering an export into the core, and checking it.
--
-- This is where the \"normalise aggressively up front\" half of the project
-- lives.  Everything the export offers that the core does not have is either
-- erased (binder annotations, @mdata@) or compiled away:
--
-- * @thm@ becomes a definition -- the kernel has no notion of a theorem -- and
--   then, where 'proofErasable' allows, an axiom;
-- * @opaque@ is checked and then becomes an axiom, since it must not unfold;
-- * reducibility hints survive as the unfolding order of 'defPriority', which
--   is advice and cannot be anything else;
-- * a declaration's recursors are /re-derived/ from the inductive
--   specification and the exported ones are required to match.
--
-- The safety flags are the exception: they are not erased, because an unsafe
-- declaration skipped the termination check and so joins a quarantined fragment
-- that the rest of the file may not mention.  See \"The unsafe fragment\" below.
--
-- That last point is the important one.  We never trust an exported recursor:
-- we build our own from "Kernel.Inductive" and then check the export agrees
-- with it.  So the file cannot smuggle in an eliminator that is stronger than
-- the one its inductive specification justifies -- an unwarranted large
-- elimination, an extra reduction rule, a bogus @k@ flag -- because any of
-- those show up as a mismatch.
module Front.Lower
  ( Config (..)
  , defaultConfig
  , checkExport
  , checkExportTrace
  , Progress (..)
  , checkStdPins
  ) where

import           Control.Monad  (foldM, forM, forM_, unless, when)
import qualified Data.ByteString.Char8 as B
import           Data.List      (find, nub, sort, zip4)
import           Data.Maybe     (isJust)
import qualified Data.Set       as S
import           Front.Export
import           Kernel.Canon
import           Kernel.Check
import           Kernel.Env
import           Kernel.Expr
import           Kernel.Inductive
import           Kernel.Level
import           Kernel.Name

-- | Everything about a run that is not the file being checked.
data Config = Config
  { cfgAccel :: !AccelMode
  , cfgSealProofs :: !Bool
    -- ^ Throw a theorem's value away once it has been checked, whenever
    -- 'proofErasable' says no reduction could ever ask for it again.  On by
    -- default: it takes the question of whether to unfold a proof off the table
    -- entirely, for all but a handful of propositions.  See SPEC.md §12.10.
  }

defaultConfig :: Config
defaultConfig = Config AccelCanonical True

-- | Check a whole export, returning the resulting environment.
checkExport :: Config -> [ExDecl] -> Either String Env
checkExport cfg = verdict . checkExportTrace cfg
  where
    verdict (Failed err  : _) = Left err
    verdict (Done env    : _) = Right env
    verdict (Starting _  : r) = verdict r
    verdict (Checked _   : r) = verdict r
    verdict []                = Left "internal error: export trace ended"

-- | What checking a declaration produced.  A trace is a 'Starting' and a
-- 'Checked' per declaration accepted, in file order, ending in exactly one
-- 'Done' or 'Failed'.
data Progress
  = Starting !(Maybe Name) -- ^ this declaration is about to be checked
  | Checked !(Maybe Name)  -- ^ this declaration went in; 'Nothing' for an empty block
  | Done Env               -- ^ every declaration went in, and the file passed
  | Failed String          -- ^ this is why it did not

-- | 'checkExport', reporting as it goes.
--
-- The list is produced lazily, and a 'Starting' is emitted -- with the
-- declaration's name already forced, so its line is parsed -- before any of that
-- declaration's checking is demanded.  A consumer reading the trace in 'IO' and
-- looking at the clock is therefore timing that declaration and nothing else,
-- and can say which one it is waiting on rather than only which one it waited
-- on.  That is the entire reason this exists: on a large export the interesting
-- question stops being /does it pass/ and becomes /which declaration is taking
-- all afternoon/, and a trace answers it in one run instead of a bisection over
-- prefixes.
checkExportTrace :: Config -> [ExDecl] -> [Progress]
checkExportTrace cfg =
  go (LS emptyEnv { envAccel = cfgAccel cfg } (cfgSealProofs cfg)
        Nothing Nothing [] [])
  where
    go st [] = [either Failed Done (finish st)]
    go st (d : ds) = case declName d of
      !nm -> Starting nm : case step st d of
        Left err  -> [Failed err]
        Right st' -> Checked nm : go st' ds

    finish st = do
      checkQuotPackage (reverse (lsQuots st))
      mapM_ (checkQuarantined (lsEnv st)) (reverse (lsUnsafe st))
      pure (lsEnv st)

    step st d = case declName d of
      Nothing -> checkDecl st d
      Just n  -> case checkDecl st d of
        Left err -> Left (showName n ++ ": " ++ err)
        Right r  -> Right r

-- | Names of the quotient primitives seen so far; needed to state the expected
-- types of the later ones.
data LS = LS
  { lsEnv     :: !Env
  , lsSeal    :: !Bool                 -- ^ 'cfgSealProofs'
  , lsQuotTy  :: !(Maybe Name)
  , lsQuotMk  :: !(Maybe Name)
  , lsQuots   :: ![(QuotKind, Name)]   -- ^ reverse order of declaration
  , lsUnsafe  :: ![(Name, [Name], Expr, Expr)]
    -- ^ @(name, universe parameters, type, value)@ of each unsafe declaration
    -- that has a value, in reverse order of declaration.  Held back until the
    -- file is finished; see 'checkQuarantined'.
  }

declName :: ExDecl -> Maybe Name
declName d = case d of
  ExAxiom  _ n _ _   -> Just n
  ExDef    _ n _ _ _ _ -> Just n
  ExThm      n _ _ _ -> Just n
  ExOpaque _ n _ _ _ -> Just n
  ExQuot     n _ _ _ -> Just n
  ExInduct (iv : _) _ _ -> Just (exiName iv)
  ExInduct [] _ _       -> Nothing

checkDecl :: LS -> ExDecl -> Either String LS
checkDecl st d = case d of
  ExAxiom u n lps ty
    | u -> quarantine st n lps ty Nothing
    | otherwise -> do
        barrier (lsEnv st) [ty]
        checkLevelParams lps
        run lps (inferSortOf ty)
        env' <- addConst (lsEnv st) (CAxiom n lps ty)
        pure st { lsEnv = env' }

  ExDef u n lps ty val h
    | u         -> quarantine st n lps ty (Just val)
    | otherwise -> defLike st n lps ty val h Retain
  -- A theorem must be a /proof/: its statement has to live in @Prop@.  (The
  -- core has no theorems, so this is the one thing lost when we turn it into a
  -- definition, and it has to be checked here.)  There is no unsafe theorem:
  -- the format gives @thm@ no safety field at all.
  ExThm n lps ty val -> do
    checkLevelParams lps
    barrier (lsEnv st) [ty, val]
    run lps $ do
      l <- inferSortOf ty
      unless (levelEquiv l LZero) $
        throwTC ("theorem statement is not a proposition: it lives in Sort "
                 ++ showLevel l)
    defLike st n lps ty val HOpaque SealIfSpent
  -- An opaque constant is checked exactly like a definition and then sealed:
  -- the kernel must not unfold it, so it enters the environment as an axiom.
  ExOpaque u n lps ty val
    | u         -> quarantine st n lps ty (Just val)
    | otherwise -> defLike st n lps ty val HOpaque Seal

  ExQuot n lps ty kind -> do
    checkLevelParams lps
    run lps (inferSortOf ty)
    when (kind == QLift) $ checkEqShape (lsEnv st)
    expected <- expectedQuot st kind n lps
    run lps $ do
      ok <- isDefEq ty expected
      unless ok $ throwTC ("quotient primitive has the wrong type\n  declared "
                           ++ showExpr ty ++ "\n  expected " ++ showExpr expected)
    env' <- addConst (lsEnv st) (CQuot n lps ty kind)
    pure st { lsEnv  = env' { envQuotInit = True }
            , lsQuotTy = if kind == QType then Just n else lsQuotTy st
            , lsQuotMk = if kind == QCtor then Just n else lsQuotMk st
            , lsQuots  = (kind, n) : lsQuots st }

  ExInduct types ctors recs -> do
    u <- blockSafety types ctors recs
    env' <- if u
              then quarantineBlock (lsEnv st) types ctors recs
              else do barrier (lsEnv st)
                        (  map exiType types ++ map excType ctors
                        ++ map exrType recs
                        ++ [exuRhs ru | rv <- recs, ru <- exrRules rv ])
                      checkInductive (lsEnv st) types ctors recs
    pure st { lsEnv = env' }
  where
    run lps act = either Left (const (Right ())) (runTC (lsEnv st) lps act)

-- | What becomes of a declaration's value once it has been checked.
data Sealing
  = Retain        -- ^ a definition: the value stays, and delta may unfold it
  | Seal          -- ^ @opaque@: the value is checked and then thrown away
  | SealIfSpent   -- ^ @thm@: thrown away unless reduction could still need it
  deriving Eq

defLike :: LS -> Name -> [Name] -> Expr -> Expr -> Hint -> Sealing
        -> Either String LS
defLike st n lps ty val hint sealing = do
  checkLevelParams lps
  barrier (lsEnv st) [ty, val]
  (spent, lic) <- runTCLearn (lsEnv st) lps $ do
    sort <- inferSortOf ty
    checkType val ty
    -- Asked in the same run as the check, so it reuses its memo tables; asked
    -- of the /statement/, so it costs a head normalisation and nothing more.
    if sealing == SealIfSpent && isDefinitelyZero sort
      then proofErasable ty
      else pure False
  let sealed = sealing == Seal || (spent && lsSeal st)
      info | sealed    = CAxiom n lps ty
           | otherwise = CDef DefInfo { defName   = n
                                      , defLevels = lps
                                      , defType   = ty
                                      , defValue  = val
                                      , defHint   = hint }
  -- Carrying the licences forward is what stops every declaration that touches
  -- arithmetic from re-establishing the same facts about @Nat.add@; see
  -- 'Licences'.
  env' <- addConst (lsEnv st) { envLicence = lic } info
  pure st { lsEnv = env' }

-- | A declaration may not bind the same universe parameter twice.
checkLevelParams :: [Name] -> Either String ()
checkLevelParams lps
  | length (nub lps) == length lps = Right ()
  | otherwise = Left "duplicate universe parameter"

-- The unsafe fragment ---------------------------------------------------------------
--
-- A declaration marked @unsafe@ or @partial@ was accepted by the elaborator
-- /without/ the termination check.  @unsafe def loop : False := loop@ is such a
-- declaration, so the unsafe fragment of any file is presumed inconsistent and
-- the whole of its content is the barrier that keeps it away from the rest.
-- See SPEC.md §12.7.

-- | Admit an unsafe constant: check its declared type is a type, then enter it
-- as an axiom and mark it.
--
-- An axiom never unfolds, so the unsafe fragment contributes no definitional
-- equalities to the file at all; it is a set of names with types attached.  Its
-- value, if it has one, is set aside for 'checkQuarantined'.
quarantine :: LS -> Name -> [Name] -> Expr -> Maybe Expr -> Either String LS
quarantine st n lps ty mval = do
  checkLevelParams lps
  _ <- runTC (lsEnv st) lps (inferSortOf ty)
  env' <- addConst (lsEnv st) (CAxiom n lps ty)
  pure st { lsEnv    = env' { envUnsafe = S.insert n (envUnsafe env') }
          , lsUnsafe = maybe id (\v -> ((n, lps, ty, v) :)) mval (lsUnsafe st) }

-- | An unsafe definition's value, checked once the file is over.
--
-- The exemption the @unsafe@ marker buys is termination, and nothing else, so
-- the value is checked against the declared type exactly as a safe one would
-- be.  What makes that possible is *when*: by the end of the file every unsafe
-- constant is in the environment as an axiom of its declared type, so
--
-- > unsafe def loop : False := loop
--
-- typechecks -- @loop@ on the right is the axiom -- and so does a mutual group
-- in which @m01@ calls @m02@ and @m02@ calls @m01@, for which no declaration
-- order works.  Deferring is what replaces the well-founded recursion the
-- elaborator did not require.
--
-- This is not a soundness measure: the fragment is quarantined by 'barrier'
-- whatever the check says.  It is there because \"unsafe\" names one specific
-- exemption, and a checker that silently granted the rest of them would be
-- describing itself wrongly.  It catches, for instance, a call with the wrong
-- number of universe arguments, or a reference to a constant the file never
-- declares.
--
-- Because the environment used is the finished one, an unsafe declaration may
-- refer forward to a constant declared after it. Restricting that would need
-- the mutual group's membership taken on trust from the @all@ field, and would
-- buy nothing: the safe fragment cannot see any of these names either way.
checkQuarantined :: Env -> (Name, [Name], Expr, Expr) -> Either String ()
checkQuarantined env (n, lps, ty, val) =
  either (Left . ((showName n ++ ": ") ++)) (const (Right ()))
         (runTC env lps (checkType val ty))

-- | An inductive block marked unsafe: every declared constant becomes an
-- uninterpreted axiom of its declared type, quarantined.
--
-- Nothing is derived and nothing is compared. Positivity is not checked --
-- @UI.mk : (UI -> UI) -> UI@ is exactly the sort of thing the marker exists to
-- allow -- and no recursor is built, so the declared recursor gets no reduction
-- rules and the declared @rules@, @numParams@, @cidx@ and @k@ are never
-- consulted.  A recursor for a non-positive type is a proof of @False@ waiting
-- to happen; here it is an axiom that no safe declaration may name.
--
-- The order matters: the type formers go in first, because the constructors'
-- and recursors' types mention them.
quarantineBlock :: Env -> [ExInd] -> [ExCtor] -> [ExRec] -> Either String Env
quarantineBlock env0 types ctors recs =
    foldM one env0 (  [ (exiName i, exiLevels i, exiType i) | i <- types ]
                   ++ [ (excName c, excLevels c, excType c) | c <- ctors ]
                   ++ [ (exrName r, exrLevels r, exrType r) | r <- recs ])
  where
    one env (n, lps, ty) = do
      checkLevelParams lps
      _ <- either (Left . ((showName n ++ ": ") ++)) Right
             (runTC env lps (inferSortOf ty))
      env' <- addConst env (CAxiom n lps ty)
      pure env' { envUnsafe = S.insert n (envUnsafe env') }

-- | Is this block unsafe?  All of it, or none of it.
--
-- The format puts an @isUnsafe@ flag on each type, each constructor and each
-- recursor separately, but they are one declaration and there is no coherent
-- reading of a mixture.  A safe constructor of an unsafe type is a safe way
-- into the unsafe fragment; an unsafe constructor of a safe type would leave
-- the kernel deriving a recursor whose minor premises quantify over a
-- constructor it has quarantined.  Neither is a file any elaborator produces.
blockSafety :: [ExInd] -> [ExCtor] -> [ExRec] -> Either String Bool
blockSafety types ctors recs
  | all snd flags = Right True
  | any snd flags = Left ("this block is marked unsafe in some places and safe \
                          \in others: " ++ commas
                            [ showName n ++ " is " ++ (if u then "unsafe" else "safe")
                            | (n, u) <- flags ])
  | otherwise     = Right False
  where
    flags =  [ (exiName i, exiIsUnsafe i) | i <- types ]
          ++ [ (excName c, excIsUnsafe c) | c <- ctors ]
          ++ [ (exrName r, exrIsUnsafe r) | r <- recs ]

-- | A safe declaration may not mention an unsafe constant.
--
-- This one rule is what the whole quarantine rests on.  An unsafe constant is
-- an axiom of a type nobody checked a witness for, so it is exactly as strong
-- as its own statement: @loop : False@ /is/ a proof of @False@ to anything
-- allowed to write it down.  The unsafe fragment is therefore treated as a
-- separate, presumed-inconsistent environment that the safe one cannot see.
--
-- Transitivity is free.  If a safe declaration @A@ mentions a safe @B@ which
-- mentions an unsafe @C@, then @B@ was rejected when it was read and @A@ never
-- gets the chance -- so a single non-recursive scan of each declaration's own
-- type and value is a complete check.
--
-- The scan covers 'Proj', whose structure name is a reference to a declaration
-- just as a @Const@ node is.  It does not need to cover numerals and string
-- literals: their typing and expansion rules (§5.2, §6.3) fire only against
-- constants matching a stored canonical /inductive/ shape, and an unsafe @Nat@
-- is an axiom, which fails that test before the barrier is reached.
barrier :: Env -> [Expr] -> Either String ()
barrier env es
  | S.null bad = Right ()
  | otherwise  = Left ("a safe declaration may not mention the unsafe "
                       ++ (if S.size bad == 1 then "constant " else "constants ")
                       ++ commas (map showName (S.toList bad)))
  where
    bad = S.intersection (S.unions (map constsOf es)) (envUnsafe env)

commas :: [String] -> String
commas = foldr1 (\a b -> a ++ ", " ++ b)

-- Inductive declarations ----------------------------------------------------------

checkInductive :: Env -> [ExInd] -> [ExCtor] -> [ExRec] -> Either String Env
checkInductive _ [] _ _ = Left "inductive declaration with no types"
checkInductive env types ctors recs = do
      let iv0       = head types
          lvls      = exiLevels iv0
          nps       = exiNumParams iv0
          declNames = map exiName types
          nDecl     = length types
      checkLevelParams lvls
      unless (length (nub declNames) == nDecl) $
        Left "inductive: the block declares the same type twice"
      forM_ types $ \iv -> do
        unless (exiLevels iv == lvls) $
          Left "inductive: the types of a block must share their universe parameters"
        unless (exiNumParams iv == nps) $
          Left "inductive: the types of a block must share their parameter count"
        unless (exiAll iv == declNames) $
          Left "inductive: \"all\" does not list the types of its block"
        unless (exiNumNested iv == exiNumNested iv0) $
          Left "inductive: the types of a block disagree about their nesting"
      groups <- mapM (mapM findCtor . exiCtors) types
      unless (length (concat groups) == length ctors) $
        Left "inductive: \"ctors\" does not list every exported constructor"
      unless (length (nub (map excName ctors)) == length ctors) $
        Left "inductive: a constructor is listed twice"

      -- Nested occurrences become extra members of the block; from here on
      -- everything is flat and "Kernel.Inductive" can take it.
      let paramTele = fst (unPisN nps (exiType iv0))
      unless (nps >= 0 && length paramTele == nps) $
        Left ("inductive: declares " ++ show nps ++ " parameters but its type has "
              ++ show (length paramTele))
      (declCtorTys, nested) <- runTC env lvls $
        planNesting (exiNumNested iv0) nps lvls paramTele declNames
                    [ excType c | c <- concat groups ]
      unless (length nested == exiNumNested iv0) $
        Left ("inductive: the block has " ++ show (length nested)
              ++ " nested occurrence(s) but declares " ++ show (exiNumNested iv0))

      let recNameOf iv = mkStr iv (B.pack "rec")
          auxRecName i = mkStr (exiName iv0) (B.pack ("rec_" ++ show i))
          declMembers =
            [ CoreMember { cmName    = exiName iv
                         , cmArity   = exiType iv
                         , cmCtors   = zip (map excName g) tys
                         , cmRecName = recNameOf (exiName iv)
                         }
            | (iv, g, tys) <- zip3 types groups (regroup (map length groups)
                                                         declCtorTys) ]
          auxMembers =
            [ CoreMember { cmName    = nsAux n
                         , cmArity   = nsArity n
                         , cmCtors   = nsCtors n
                         , cmRecName = auxRecName i
                         }
            | (i, n) <- zip [1 :: Int ..] nested ]
          ourRecNames = map recNameOf declNames
                     ++ [ auxRecName i | i <- [1 .. length nested] ]
      -- The eliminators of a block are exactly these and nothing else.  Without
      -- this an export could park an extra, differently named recursor beside
      -- the ones its inductive specification justifies.
      unless (sort (map exrName recs) == sort ourRecNames) $
        Left ("the block's recursors are " ++ show (map showName (sort (map exrName recs)))
              ++ ", expected " ++ show (map showName (sort ourRecNames)))

      ab <- admitBlock env CoreBlock
        { cbLevels    = lvls
        , cbNumParams = nps
        , cbMembers   = declMembers ++ auxMembers
        , cbElimHint  = elimHint (map exrLevels recs) lvls
        }

      -- Drop the auxiliary members and put the real containers back.
      let unnest | null nested = id
                 | otherwise   = applyAux lvls nps nested
          inds  = take nDecl (abInds ab)
          ourCs = [ [ ci { ctorType = excType c } | (ci, c) <- zip g cs ]
                  | (g, cs) <- zip (take nDecl (abCtors ab)) groups ]
          ourRs = [ r { recType   = unnest (recType r)
                      , recInduct = unAux nested (recInduct r)
                      , recRules  = [ ru { rrCtor = unAux nested (rrCtor ru)
                                         , rrRhs  = unnest (rrRhs ru) }
                                    | ru <- recRules r ]
                      }
                  | r <- abRecs ab ]

      -- The export's own bookkeeping must agree with what we derived.
      let blockRec  = any indIsRecursive (abInds ab)
          blockRefl = or (abReflexive ab)
      forM_ (zip4 types inds (take nDecl (abReflexive ab)) ourCs) $ \(iv, ind, refl, ourG) -> do
        unless (exiNumIndices iv == indNumIndices ind) $
          Left (showName (exiName iv) ++ " declares " ++ show (exiNumIndices iv)
                ++ " indices, but its type has " ++ show (indNumIndices ind))
        derivedFlag "isRec" (exiName iv) (exiIsRec iv)
                    (indIsRecursive ind) blockRec
        derivedFlag "isReflexive" (exiName iv) (exiIsReflexive iv)
                    refl blockRefl
        forM_ (zip3 [0 ..] (exiCtors iv) ourG) $ \(k, cn, ourC) -> do
          c <- findCtor cn
          unless (excInduct c == exiName iv) $ Left "constructor of the wrong type"
          unless (excLevels c == lvls) $
            Left "constructor has different universe parameters from its type"
          unless (excIdx c == k) $
            Left ("constructor " ++ showName cn ++ " has the wrong index")
          unless (excNumParams c == nps) $
            Left ("constructor " ++ showName cn ++ " has the wrong numParams")
          unless (excNumFields c == ctorNumFields ourC) $
            Left ("constructor " ++ showName cn ++ " declares "
                  ++ show (excNumFields c) ++ " fields but has "
                  ++ show (ctorNumFields ourC))

      envInd <- foldM addConst env
        (map CInd inds ++ map CCtor (concat ourCs) ++ map CRec ourRs)
      -- Unnesting rebuilt these terms behind the kernel's back, so for a nested
      -- block they get audited again against the real containers.
      unless (null nested) $ forM_ ourRs $ \r ->
        either (\e -> Left ("recursor " ++ showName (recName r)
                            ++ " does not typecheck after unnesting: " ++ e))
               (const (Right ()))
               (runTC envInd (recLevels r) (inferSortOf (recType r)))
      forM_ ourRs $ \r -> case find ((== recName r) . exrName) recs of
        Nothing -> Left ("no exported recursor named " ++ showName (recName r))
        Just rv -> checkRecursorMatches envInd declNames rv r
      pure envInd
  where
    findCtor n = case find ((== n) . excName) ctors of
      Just c  -> Right c
      Nothing -> Left ("no exported constructor named " ++ showName n)
    -- Reuse the export's name for the fresh elimination universe when it has
    -- one, so that the derived recursor type is literally the same term.
    elimHint recLpss indLps = case [ h | (h : t) <- recLpss
                                       , length t == length indLps ] of
      (h : _) -> h
      _       -> str "u"
    regroup [] _       = []
    regroup (k : ks) xs = let (a, b) = splitAt k xs in a : regroup ks b

-- | A boolean the export restates that the kernel also derives.
--
-- @isRec@ and @isReflexive@ are, in the format's own words, \"informational
-- fields\" the elaborator computed; no rule in this kernel reads them off the
-- file.  They are still checked, for the reason every other redundant field is
-- (SPEC.md §1): a number or flag the export supplies and nobody verifies is a
-- place where a file can say one thing and mean another, and the cost of
-- closing it is one comparison.
--
-- The two bounds are what makes this safe on a mutual block.  @lo@ is what this
-- member's own constructors force the flag to be; @hi@ is what the block as a
-- whole permits.  For a single-member block they coincide and the check is
-- exact.  For a mutual block they can differ -- a member with no recursive
-- field of its own inside a block that has one -- and the format does not say
-- whether the flag describes the member or its block.  Rather than guess, a
-- value is rejected only when it is wrong under /both/ readings.
derivedFlag :: String -> Name -> Bool -> Bool -> Bool -> Either String ()
derivedFlag what n declared lo hi
  | declared, not hi = bad "false"
  | not declared, lo = bad "true"
  | otherwise        = Right ()
  where
    bad want = Left (showName n ++ " is declared with " ++ what ++ " = "
                     ++ lc declared ++ ", but the kernel derives " ++ want)
    lc b = if b then "true" else "false"

-- | Require the exported recursor to be the one we derived.
checkRecursorMatches :: Env -> [Name] -> ExRec -> RecInfo -> Either String ()
checkRecursorMatches env allInds rv r = do
  -- A recursor's "all" names the inductive types of its mutual block, not the
  -- other recursors, and not the auxiliary members nesting introduced.
  unless (exrAll rv == allInds) $
    Left "recursor: \"all\" does not list the types of its inductive block"
  unless (exrNumParams rv == recNumParams r) $
    Left ("recursor declares " ++ show (exrNumParams rv) ++ " parameters, expected "
          ++ show (recNumParams r))
  unless (exrNumMotives rv == recNumMotives r) $
    Left ("recursor declares " ++ show (exrNumMotives rv) ++ " motives, expected "
          ++ show (recNumMotives r))
  unless (exrNumIndices rv == recNumIndices r) $
    Left ("recursor declares " ++ show (exrNumIndices rv) ++ " indices, expected "
          ++ show (recNumIndices r))
  unless (exrNumMinors rv == recNumMinors r) $
    Left ("recursor declares " ++ show (exrNumMinors rv) ++ " minor premises, expected "
          ++ show (recNumMinors r))
  unless (exrK rv == recK r) $
    Left ("recursor declares k = " ++ show (exrK rv) ++ ", expected " ++ show (recK r))
  -- Positional, so a repeated name would make the substitution below ambiguous.
  checkLevelParams (exrLevels rv)
  unless (length (exrLevels rv) == length (recLevels r)) $
    Left ("recursor has " ++ show (length (exrLevels rv))
          ++ " universe parameters, expected " ++ show (length (recLevels r))
          ++ (if length (recLevels r) > length (exrLevels rv)
                then " (its inductive type supports large elimination)"
                else " (its inductive type does not support large elimination)"))
  unless (length (exrRules rv) == length (recRules r)) $
    Left ("recursor has " ++ show (length (exrRules rv)) ++ " reduction rules, expected "
          ++ show (length (recRules r)))
  either Left (const (Right ())) $ runTC env (recLevels r) $ do
    let ours = map LParam (recLevels r)
        theirs :: Expr -> Expr
        theirs = instLevelsE (exrLevels rv) ours
    okTy <- isDefEq (theirs (exrType rv)) (recType r)
    unless okTy $ do
      d <- whnf (recType r)
      throwTC ("the declared recursor type is not the one this inductive type\
               \ justifies\n  declared " ++ showExpr (theirs (exrType rv))
               ++ "\n  derived  " ++ showExpr d)
    forM_ (exrRules rv) $ \ru -> case find ((== exuCtor ru) . rrCtor) (recRules r) of
      Nothing -> throwTC ("reduction rule for unknown constructor "
                          ++ showName (exuCtor ru))
      Just our -> do
        unless (exuNumFields ru == rrNumFields our) $
          throwTC ("reduction rule for " ++ showName (exuCtor ru) ++ " declares "
                   ++ show (exuNumFields ru) ++ " fields, expected "
                   ++ show (rrNumFields our))
        okR <- isDefEq (theirs (exuRhs ru)) (rrRhs our)
        unless okR $
          throwTC ("the declared reduction rule for " ++ showName (exuCtor ru)
                   ++ " is not the one iota gives\n  declared "
                   ++ showExpr (theirs (exuRhs ru))
                   ++ "\n  derived  " ++ showExpr (rrRhs our))

-- Nested inductives ------------------------------------------------------------------
--
-- A nested inductive is one whose constructors mention it underneath some
-- /other/, already admitted, type constructor:
--
-- > inductive Syntax | node : SyntaxNodeKind -> Array Syntax -> Syntax | ...
--
-- The core has no rule for that: strict positivity only recognises an
-- occurrence as the head of a field's result.  The standard reading is that
-- @Array Syntax@ is a copy of @Array@ specialised at @Syntax@, mutually
-- recursive with it -- so that is literally what we build.  Each distinct
-- occurrence becomes an extra member of the block under an internal name, with
-- the container's own constructors specialised to it, and the whole thing is
-- then an ordinary mutual block.
--
-- The point of doing it this way is that the specialised copies go through the
-- /same/ positivity and universe checks as everything else.  Unsound nesting is
-- caught by those checks and not by a special case: nesting inside @fun a => a
-- -> False@ turns into a member with a negative field, and the @ctor@ judgement
-- rejects it.
--
-- Once the recursors are derived, the internal names are replaced by the
-- containers they stood for and the result is re-checked.  Nothing internal ever
-- reaches the environment.

-- | One nested occurrence and the block member that replaces it.
data Nested = Nested
  { nsAux     :: !Name            -- ^ internal name of the member
  , nsHead    :: !Name            -- ^ the container it is a copy of
  , nsLevels  :: ![Level]         -- ^ the container's universe arguments
  , nsArgs    :: ![Expr]          -- ^ its parameters, de Bruijn over the block's
  , nsArity   :: !Expr
  , nsCtors   :: ![(Name, Expr)]  -- ^ under internal names
  , nsCtorMap :: ![(Name, Name)]  -- ^ internal constructor name -> the real one
  }

-- | A container applied to arguments that mention the block.
type Occ = (Name, [Level], [Expr])

-- | Find every nested occurrence and build the members that replace them,
-- returning also the block's own constructor types with the occurrences
-- rewritten.  A block with no nesting is passed through untouched.
planNesting :: Int -> Int -> [Name] -> [(Binder, Expr)] -> [Name] -> [Expr]
            -> TC ([Expr], [Nested])
planNesting cap nps lvls paramTele declNames declCtorTys =
  withLocals paramTele $ \ps -> do
    env <- getEnv
    opened <- mapM (instParams nps (map FVar ps)) declCtorTys
    found  <- discover env [] opened
    if null found then pure (declCtorTys, []) else do
      let auxNames = [ mkNum (mkStr (head declNames) (B.pack "_nested")) i
                     | i <- [1 .. toInteger (length found)] ]
          tagged   = zip found auxNames
          rw       = rewriteNested tagged ps (map LParam lvls)
          close e  = mkPis paramTele (abstractFVars ps e)
      ns <- forM tagged $ \((c, us, pargs), aux) -> do
        ind   <- indAt c
        arity <- instParams (indNumParams ind) pargs
                            (instLevelsE (indLevels ind) us (indType ind))
        -- The block may only be nested in the container's /parameters/: an
        -- index is not a positive position, and a member occurring in one would
        -- silently be dropped by the specialisation.
        unless (all (\n -> not (occursConst n arity)) declNames) $
          throwTC ("nested inductive: " ++ showName c
                   ++ " is nested at an argument that reaches its indices")
        cs <- forM (zip [0 :: Integer ..] (indCtors ind)) $ \(k, cn) -> do
          ci  <- ctorAt cn
          cty <- instParams (ctorNumParams ci) pargs
                            (instLevelsE (ctorLevels ci) us (ctorType ci))
          pure (mkNum (mkStr aux (B.pack "ctor")) k, close (rw cty), cn)
        pure Nested { nsAux     = aux
                    , nsHead    = c
                    , nsLevels  = us
                    , nsArgs    = map (abstractFVars ps) pargs
                    , nsArity   = close arity
                    , nsCtors   = [ (n, t) | (n, t, _) <- cs ]
                    , nsCtorMap = [ (n, r) | (n, _, r) <- cs ]
                    }
      pure (map (close . rw) opened, ns)
  where
    -- Worklist: scan a term for occurrences, then scan the constructors of
    -- whatever containers it turned up, until nothing new appears.  Every step
    -- moves to a container declared strictly earlier, so this terminates; the
    -- cap is only there to turn a surprise into a message.
    --
    -- The queue is first in, first out, and 'collectNested' does not look
    -- inside an occurrence it has just reported, so the copies come out one
    -- level of nesting at a time: the containers wrapping the block itself,
    -- then the containers wrapping those, and so on.  Order matters -- it is
    -- the order of the auxiliary members, hence of the motives and minor
    -- premises of every recursor in the block, and the export's recursors have
    -- to match ours exactly.
    discover _   found []       = pure (reverse found)
    discover env found (t : ts) = do
      let news = pick found (collectNested env declNames t)
      unless (length found + length news <= cap) $
        throwTC "nested inductive: more nested occurrences than the file declares"
      more <- concat <$> mapM ctorTypesAt news
      discover env (reverse news ++ found) (ts ++ more)
    pick found = go []
      where
        go acc []       = reverse acc
        go acc (o : os) | o `elem` found || o `elem` acc = go acc os
                        | otherwise                      = go (o : acc) os

    ctorTypesAt (c, us, pargs) = do
      ind <- indAt c
      forM (indCtors ind) $ \cn -> do
        ci <- ctorAt cn
        instParams (ctorNumParams ci) pargs
                   (instLevelsE (ctorLevels ci) us (ctorType ci))

    indAt c = getEnv >>= \env -> case lookupConst env c of
      Just (CInd ind) -> pure ind
      _ -> throwTC ("nested inductive: " ++ showName c ++ " is not an inductive type")
    ctorAt cn = getEnv >>= \env -> case lookupConst env cn of
      Just (CCtor ci) -> pure ci
      _ -> throwTC ("nested inductive: " ++ showName cn ++ " is not a constructor")

-- | Peel @k@ leading @Pi@ binders, substituting the given arguments.
instParams :: Int -> [Expr] -> Expr -> TC Expr
instParams 0 _ ty = pure ty
instParams k (a : as) ty = do
  (_, cod) <- ensurePi ty
  instParams (k - 1) as (inst1 a cod)
instParams _ [] _ = throwTC "nested inductive: not enough parameter arguments"

-- | Every subterm of the form @C p̄ ī@ where @C@ is an already admitted
-- inductive type and some member of the block occurs in its parameters @p̄@.
--
-- An occurrence whose parameters mention a bound variable is skipped: the copy
-- would have to depend on it, and there is no such member.  The block's own name
-- is then left where it is and strict positivity rejects it.
--
-- The search stops /at/ an occurrence: it reports @C p̄@ and then looks only
-- inside the indices @ī@, never inside @p̄@.  Nothing is lost, because whatever
-- is nested in @p̄@ and actually matters reappears in @C@'s own constructor
-- types once they are specialised at @p̄@ -- one round of 'discover' later
-- rather than immediately.  That delay is the point: it makes the copies come
-- out breadth first, which is the order the export lists the motives and minor
-- premises of a nested block's recursor in.  (It also silently drops an
-- occurrence buried in a parameter that @C@ never uses: no constructor could
-- mention the copy, so there is no reason to make one.)
collectNested :: Env -> [Name] -> Expr -> [Occ]
collectNested env declNames = go
  where
    go e = case here e of
      Just (o, ixargs) -> o : concatMap go ixargs
      Nothing          -> sub e
    here e = case unApps e of
      (Const c us, args)
        | Just (CInd ind) <- lookupConst env c
        , let (pargs, ixargs) = splitAt (indNumParams ind) args
        , length args >= indNumParams ind
        , all ((== 0) . looseBVarRange) pargs
        , any (\n -> any (occursConst n) pargs) declNames
        -> Just ((c, us, pargs), ixargs)
      _ -> Nothing
    sub e = case e of
      App f a     -> go f ++ go a
      Lam _ t b   -> go t ++ go b
      Pi _ t b    -> go t ++ go b
      Let _ t v b -> go t ++ go v ++ go b
      Proj _ _ s  -> go s
      _           -> []

-- | Replace each nested occurrence by the block member standing for it.
rewriteNested :: [(Occ, Name)] -> [Int] -> [Level] -> Expr -> Expr
rewriteNested tagged ps selfL = go
  where
    go e = case unApps e of
      (Const c us, args)
        | Just (aux, np) <- match c us args ->
            mkApps (Const aux selfL) (map FVar ps ++ map go (drop np args))
      (h, args)
        | null args -> goHead h
        | otherwise -> mkApps (goHead h) (map go args)
    goHead e = case e of
      Lam n t b   -> Lam n (go t) (go b)
      Pi n t b    -> Pi n (go t) (go b)
      Let n t v b -> Let n (go t) (go v) (go b)
      Proj tn i s -> Proj tn i (go s)
      _           -> e
    match c us args = case [ (aux, np)
                           | ((c', us', pargs), aux) <- tagged
                           , c' == c, us' == us
                           , let np = length pargs
                           , length args >= np
                           , take np args == pargs ] of
      (r : _) -> Just r
      []      -> Nothing

-- | Undo 'rewriteNested' on a derived term.
--
-- An auxiliary member is always applied to the block's parameters first, so the
-- replacement is the container at those parameters; substituting at the head of
-- the spine beta-reduces on the spot, and what comes back out is exactly the
-- term the export wrote.
applyAux :: [Name] -> Int -> [Nested] -> Expr -> Expr
applyAux lvls nps ns = go
  where
    subs = [ (nsAux n, nsHead n, nsLevels n, nsArgs n) | n <- ns ]
        ++ [ (i, r, nsLevels n, nsArgs n) | n <- ns, (i, r) <- nsCtorMap n ]
    go e = case unApps e of
      (Const c us, args)
        | Just (tgt, tls, pargs) <- match c, length args >= nps ->
            let (pre, rest) = splitAt nps (map go args)
            in mkApps (Const tgt (map (instLevelParams lvls us) tls))
                      (map (instN (reverse pre)) pargs ++ rest)
      (h, args)
        | null args -> goHead h
        | otherwise -> mkApps (goHead h) (map go args)
    goHead e = case e of
      Lam n t b   -> Lam n (go t) (go b)
      Pi n t b    -> Pi n (go t) (go b)
      Let n t v b -> Let n (go t) (go v) (go b)
      Proj tn i s -> Proj tn i (go s)
      _           -> e
    match c = case [ (t, l, p) | (a, t, l, p) <- subs, a == c ] of
      (r : _) -> Just r
      []      -> Nothing

-- | The real name behind an internal one.
unAux :: [Nested] -> Name -> Name
unAux ns n = head ([ nsHead x | x <- ns, nsAux x == n ]
                ++ [ r | x <- ns, (i, r) <- nsCtorMap x, i == n ]
                ++ [n])

-- Quotient primitives ---------------------------------------------------------------
--
-- @Quot@ is the one piece of the theory that is neither an inductive type nor
-- an axiom: its eliminator computes, but only on @Quot.mk@, and unlike a
-- derived recursor it demands a proof that the function respects the relation.
-- That extra argument is exactly what keeps @Quot.sound@ consistent, so the
-- four types are pinned down here rather than taken on trust.

-- | The quotient package is one extension to the theory, not four independent
-- constants, and it is admitted whole or not at all.
--
-- The model that justifies it reads @Quot α r@ as the set of equivalence
-- classes, @Quot.mk@ as the class map, and the two eliminators as the functions
-- that factor through it; @Quot.sound@ is then true by construction.  A file
-- that declares only some of the four is asking for a fragment of that
-- extension.  Every fragment happens to be sound on its own -- dropping an
-- eliminator only makes the type harder to use -- so this rule is not what
-- stands between the kernel and a false proof.  It is a conformance rule: the
-- elaborator introduces the four together and every real export carries them
-- together, so a file with three of them was assembled by something that is not
-- an exporter, and the honest response is to say so rather than to guess what
-- the missing one was meant to be.
--
-- The check is on /kinds/, not names.  Nothing in the theory cares what the
-- primitives are called -- 'expectedQuot' ties each one to the type and the
-- constructor the file itself declared, not to a spelling -- so a package named
-- differently is still a package.  What is not allowed is a second one: two
-- declarations of the same kind are two candidate constructors for one
-- quotient type, and the iota rule of SPEC.md §10 is stated for one.
--
-- @Quot.sound@ is deliberately not part of this.  It reaches the file as an
-- ordinary axiom rather than as a @quot@ line, 7 of the 9 arena exports that
-- use quotients leave it out entirely, and leaving it out is a weakening.
--
-- SPEC.md §12.3.
checkQuotPackage :: [(QuotKind, Name)] -> Either String ()
checkQuotPackage []  = Right ()
checkQuotPackage kns = mapM_ one [QType, QCtor, QLift, QInd]
  where
    one k = case [n | (k', n) <- kns, k' == k] of
      [_] -> Right ()
      []  -> Left ("the quotient package is incomplete: nothing of kind "
                   ++ show (quotKindName k) ++ " is declared, but the file has "
                   ++ commas [ showName n ++ " (" ++ quotKindName k' ++ ")"
                             | (k', n) <- kns ])
      ns  -> Left ("the quotient package is declared more than once: "
                   ++ commas (map showName ns) ++ " all have kind "
                   ++ show (quotKindName k))

-- | A quotient kind as the export format spells it.
quotKindName :: QuotKind -> String
quotKindName k = case k of
  QType -> "type"
  QCtor -> "ctor"
  QLift -> "lift"
  QInd  -> "ind"

-- | The type each quotient primitive is required to have.
expectedQuot :: LS -> QuotKind -> Name -> [Name] -> Either String Expr
expectedQuot st kind self lps = case (kind, lps) of
  (QType, [u]) -> Right $
    pi_ "α" (Sort (LParam u)) $
    pi_ "r" rel $
    Sort (LParam u)

  (QCtor, [u]) -> do
    qt <- needQuotTy
    Right $
      pi_ "α" (Sort (LParam u)) $
      pi_ "r" rel $
      pi_ "_" (BVar 1) $
      quotAt qt u [BVar 2, BVar 1]

  (QLift, [u, v]) -> do
    qt <- needQuotTy
    Right $
      pi_ "α" (Sort (LParam u)) $
      pi_ "r" rel $
      pi_ "β" (Sort (LParam v)) $
      pi_ "f" (pi_ "_" (BVar 2) (BVar 1)) $
      pi_ "h" (pi_ "a" (BVar 3) $
               pi_ "b" (BVar 4) $
               pi_ "_" (mkApps (BVar 4) [BVar 1, BVar 0]) $
               mkApps (Const nameEq [LParam v])
                      [BVar 4, App (BVar 3) (BVar 2), App (BVar 3) (BVar 1)]) $
      pi_ "q" (quotAt qt u [BVar 4, BVar 3]) $
      BVar 3

  (QInd, [u]) -> do
    qt <- needQuotTy
    qmk <- needQuotMk
    Right $
      pi_ "α" (Sort (LParam u)) $
      pi_ "r" rel $
      pi_ "β" (pi_ "_" (quotAt qt u [BVar 1, BVar 0]) (Sort LZero)) $
      pi_ "h" (pi_ "a" (BVar 2) $
               App (BVar 1) (mkApps (Const qmk [LParam u]) [BVar 3, BVar 2, BVar 0])) $
      pi_ "q" (quotAt qt u [BVar 3, BVar 2]) $
      App (BVar 2) (BVar 0)

  _ -> Left ("quotient primitive has " ++ show (length lps)
             ++ " universe parameters, which is not what its kind takes")
  where
    -- r : α → α → Prop, stated one binder in from α
    rel = pi_ "_" (BVar 0) (pi_ "_" (BVar 1) (Sort LZero))
    quotAt qt u as = mkApps (Const qt [LParam u]) as
    needQuotTy = maybe (Left "the quotient type must be declared first")
                       Right (if kind == QType then Just self else lsQuotTy st)
    needQuotMk = maybe (Left "Quot.mk must be declared before Quot.ind")
                       Right (lsQuotMk st)

-- | @Eq@ is the one name the quotient package borrows from the file.
--
-- @Quot.lift@'s congruence premise is @∀ a b, r a b → f a = f b@, and that @=@
-- is resolved by /name/ against whatever the file has declared.  So the file
-- chooses how strong its own obligation is.  Declaring
--
-- > Eq.refl : ∀ (α : Sort u) (x y : α), Eq α x y      -- second point a *field*
--
-- makes @Eq@ the total relation, the premise vacuous, and every function
-- liftable across every relation; combined with a @Quot.sound@ stated over a
-- second, faithful equality it collapses @Bool@ and proves @False@.  Nothing
-- else in the theory has this shape -- every other constant the kernel builds
-- into a type is one it also derives -- so @Eq@ is pinned here, before
-- @Quot.lift@ is admitted.
--
-- What the iota rule for @Quot.lift@ needs is that @Eq α x y@ be inhabited only
-- when @x ≡ y@.  For an inductive family that follows from the shape alone: the
-- sole introduction form is
--
-- > Eq.refl : ∀ (α : Sort u) (a : α), Eq α a a
--
-- which takes no fields, so any inhabitant of @Eq α x y@ whnfs to @Eq.refl α a@
-- for some @a@, and matching its type against @Eq α x y@ forces @x ≡ a ≡ y@.
--
-- The constructor is found by /position/ -- the unique constructor of @Eq@ --
-- and pinned by its /type/.  Its name is not load-bearing and is not checked:
-- an equality whose constructor is called something else is still an equality,
-- and rejecting it would be a divergence with no soundness content behind it.
checkEqShape :: Env -> Either String ()
checkEqShape env = case lookupConst env nameEq of
  Nothing -> Left "Quot.lift states its congruence premise with Eq, which is \
                  \not declared"
  Just (CInd ind)
    | [u] <- indLevels ind
    , indNumParams ind == 2
    , indNumIndices ind == 1
    , [cn] <- indCtors ind
    , Just (CCtor ci) <- lookupConst env cn
    , ctorLevels ci == [u]
    , ctorNumParams ci == 2
    , ctorNumFields ci == 0
    -> do
      let eqTy   = pi_ "α" (Sort (LParam u)) $
                   pi_ "x" (BVar 0) $
                   pi_ "y" (BVar 1) $
                   Sort LZero
          reflTy = pi_ "α" (Sort (LParam u)) $
                   pi_ "a" (BVar 0) $
                   mkApps (Const nameEq [LParam u]) [BVar 1, BVar 0, BVar 0]
      okTy   <- runTC env [u] (isDefEq (indType ind) eqTy)
      okRefl <- runTC env [u] (isDefEq (ctorType ci) reflTy)
      unless (okTy && okRefl) wrongShape
  Just _ -> wrongShape
  where
    wrongShape = Left "Eq is not equality -- Quot.lift's congruence premise \
                      \would not say that the function respects the relation"

pi_ :: String -> Expr -> Expr -> Expr
pi_ n = Pi (Binder (str n))

-- Auditing the standard constants -------------------------------------------------

-- | Compare the standard constants against the forms in "Kernel.Canon", and
-- report every one that has been declared but declared differently.
--
-- This decides nothing on its own.  The caller chooses whether a mismatch is a
-- remark or a refusal, and by default asks the question at all only when told
-- to, because the answer is not about soundness.  Everything the kernel /needs/
-- to believe about these names it checks unconditionally and separately: @Eq@
-- before @Quot.lift@ (see 'checkEqShape'), @Nat@ and @Bool@ before arithmetic
-- (see "Kernel.Canon"), the quotient types when they are admitted (§10).  What
-- is left over is the part no rule of the theory depends on -- that @False@ is
-- empty, that @propext@ says what @propext@ says -- and a file that gets that
-- part wrong is not unsound so much as not the file it appears to be.  Which is
-- worth being told about.
--
-- The three axioms are where this pays.  They are asserted, not proved, so
-- nothing about them is checked beyond their being well-formed; and each is
-- stated over constants the file owns, so the way to weaken one is to leave it
-- verbatim and redefine what it quantifies over.
checkStdPins :: Env -> [String]
checkStdPins env = concatMap one stdPins ++ quotAtomic
  where
    present n = isJust (lookupConst env n)

    one (n, p) = case lookupConst env n of
      Nothing -> []          -- not in the file; nothing to audit
      Just ci -> case p of
        PinInd c -> case runTC env (levelsOf ci) (canonIndMatches c) of
          Right True -> []
          _          -> [note n "is not the standard inductive type of that name"]

        PinAxiom k mkTy
          | not (isAxiom ci) ->
              [note n "is declared, but not as an axiom"]
          | length (levelsOf ci) /= k ->
              [note n ("has " ++ plural (length (levelsOf ci)) "universe parameter"
                       ++ ", not " ++ show k)]
          | otherwise ->
              let want = mkTy (levelsOf ci) in
              case runTC env (levelsOf ci) (isDefEq (constType ci) want) of
                Right True -> []
                _          -> [note n "does not have its standard statement"
                               ++ "\n  declared " ++ showExpr (constType ci)
                               ++ "\n  standard " ++ showExpr want]

        PinQuot k -> case ci of
          CQuot _ _ _ k' | k' == k -> []
          _ -> [note n "is not the quotient primitive of that name"]

    -- The four primitives are introduced together by the elaborator and are
    -- exported together by every real export; a file with three of them has
    -- been edited by hand, whatever else is true of it.
    quotAtomic
      | any present quotModule, not (all present quotModule) =
          [ "the quotient package is incomplete: missing "
            ++ commas [showName n | n <- quotModule, not (present n)] ]
      | otherwise = []

    isAxiom ci = case ci of CAxiom{} -> True; _ -> False
    levelsOf   = constLevels
    note n msg = showName n ++ ": " ++ msg
    plural k s = show k ++ " " ++ s ++ (if k == 1 then "" else "s")
