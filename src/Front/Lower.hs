{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE LambdaCase #-}
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
  , Obligation (..)
  , discharge
  , checkStdPins
  ) where

import           Control.Monad  (foldM, forM, forM_, unless, when)
import qualified Data.ByteString.Char8 as B
import           Data.List      (find, nub, sort)
import           Data.Maybe     (isJust)
import qualified Data.Set       as S
import           Front.Block
import           Front.Export
import           Front.Hetero
import           Kernel.Canon
import           Kernel.Check
import           Kernel.Env
import           Kernel.Expr
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
  , cfgMutUniv :: !Bool
    -- ^ Reject a mutual inductive block whose types do not all land in the same
    -- universe, as every other Lean kernel does.  Off by default: the block is
    -- sound and \"Front.Hetero\" derives it (SPEC.md §9.6).
  , cfgDefer :: !Bool
    -- ^ Hand back each definition's value check as an 'Obligation' instead of
    -- running it where it stands.  Off by default; see 'Obligation'.
  }

defaultConfig :: Config
defaultConfig = Config AccelCanonical True False False

-- | Check a whole export, returning the resulting environment.
checkExport :: Config -> [ExDecl] -> Either String Env
checkExport cfg = verdict . checkExportTrace cfg . map Right
  where
    verdict (Failed err   : _) = Left err
    verdict (Done env obs : _) = env <$ discharge obs
    verdict (Starting _   : r) = verdict r
    verdict (Checked _    : r) = verdict r
    verdict []                 = Left "internal error: export trace ended"

-- | What checking a declaration produced.  A trace is a 'Starting' and a
-- 'Checked' per declaration accepted, in file order, ending in exactly one
-- 'Done' or 'Failed'.
data Progress
  = Starting !(Maybe Name) -- ^ this declaration is about to be checked
  | Checked !(Maybe Name)  -- ^ this declaration went in; 'Nothing' for an empty block
  | Done Env [Obligation]  -- ^ every declaration went in, bar these ('cfgDefer')
  | Failed String          -- ^ this is why it did not

-- | A definition's value check, put off until the file has been walked.
--
-- Under 'cfgDefer' a definition is admitted on the strength of its /statement/
-- alone -- the type is checked to be a type, and that is what the environment
-- needs -- and the check that the value inhabits it is handed back here.  The
-- file is accepted when every obligation is.
--
-- What this buys is that the obligations are independent of each other.  A
-- value check reads an environment and returns a verdict; it writes nothing,
-- and the environment it reads is the one its own declaration was admitted in,
-- captured here, so no obligation can see another's result.  They may therefore
-- be discharged in any order, or all at once on as many cores as there are --
-- and the verdict does not depend on which, since 'discharge' always reports
-- the first failure in file order.  On @std@ the value checks are 81% of the
-- run.
--
-- It is not the default, because it is a second way to check a file and the
-- kernel should have one.  The interleaved path is the audited one: it admits a
-- declaration only once everything about it has been checked, which is the
-- invariant the rest of this module is written against.
data Obligation = Obligation
  { obName  :: !Name
    -- ^ whose value this is
  , obCheck :: Either String ()
    -- ^ the check itself, unevaluated.  Forcing this to weak head normal form
    -- /is/ performing it; there is nothing else inside.
  }

-- | Discharge obligations in file order, reporting the first failure.
discharge :: [Obligation] -> Either String ()
discharge = foldr (\o rest -> obCheck o >> rest) (Right ())

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
--
-- The input is 'Front.Export.parseExport' unchanged, a 'Left' in it being a line
-- that could not be read.  Reading is lazy, so demanding the next declaration is
-- what reads the lines up to it, and a file is read and checked in one pass over
-- it rather than two.
checkExportTrace :: Config -> [Either String ExDecl] -> [Progress]
checkExportTrace cfg =
  go (LS emptyEnv { envAccel = cfgAccel cfg } (cfgSealProofs cfg)
        (cfgMutUniv cfg) (cfgDefer cfg) Nothing Nothing [] [] [] [] 0 0)
  where
    go st [] = [either Failed (\e -> Done e (reverse (lsObs st))) (finish st)]
    go _  (Left err : _) = [Failed err]
    go st (Right d : ds) = case declName d of
      !nm -> Starting nm : case step st d of
        Left err  -> [Failed err]
        Right st' -> Checked nm : go st' ds

    finish st = do
      -- A quotient primitive still held back at the end of the file never had
      -- the rest of its package, or never fitted it; either way, say why.  It
      -- is /not/ retried here: the package is admitted where its last line is,
      -- so anything it borrows from outside itself -- @Quot.lift@ borrows @Eq@
      -- -- has to have been declared before that point, as for any other
      -- declaration.
      mapM_ (Left . qdWhy) (lsQuotPend st)
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
  , lsMutUniv :: !Bool                 -- ^ 'cfgMutUniv'
  , lsDefer   :: !Bool                 -- ^ 'cfgDefer'
  , lsQuotTy  :: !(Maybe Name)
  , lsQuotMk  :: !(Maybe Name)
  , lsQuots   :: ![(QuotKind, Name)]   -- ^ reverse order of admission
  , lsQuotPend :: ![QuotD]
    -- ^ quotient primitives read but not yet admitted, in file order; see
    -- 'quotFlush'.
  , lsUnsafe  :: ![(Name, [Name], Expr, Expr)]
    -- ^ @(name, universe parameters, type, value)@ of each unsafe declaration
    -- that has a value, in reverse order of declaration.  Held back until the
    -- file is finished; see 'checkQuarantined'.
  , lsObs     :: ![Obligation]
    -- ^ value checks put off under 'lsDefer', in reverse order of declaration.
  , lsSeen    :: !Int
    -- ^ how many of those there are, so 'lsWarmAt' can be reached.
  , lsWarmAt  :: !Int
    -- ^ the count at which to call 'warmLicences' again, doubling each time.
    --
    -- The licences cannot be established before the constants they are about
    -- have been declared, and there is no telling from here when that is; the
    -- cost of asking too early is a failed attempt, and of asking too late a
    -- run of declarations that had to establish their own.  Doubling pays for
    -- both: at most a logarithmic number of attempts over the whole file, and
    -- the first successful one no later than twice as far in as it could have
    -- been.  On @std@ everything is licensed within the first few thousand
    -- declarations of ninety thousand.
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

  -- Queued rather than admitted on the spot: the package is one extension to
  -- the theory (SPEC.md §12.3) and the file's order within it carries no
  -- meaning, so a primitive whose siblings have not arrived yet waits for them
  -- instead of being rejected.
  ExQuot n lps ty kind -> do
    checkLevelParams lps
    pure (quotFlush st { lsQuotPend = lsQuotPend st
                                        ++ [QuotD kind n lps ty "not checked"] })

  ExInduct types ctors recs -> do
    u <- blockSafety types ctors recs
    env' <- if u
              then quarantineBlock (lsEnv st) types ctors recs
              else do barrier (lsEnv st)
                        (  map exiType types ++ map excType ctors
                        ++ map exrType recs
                        ++ [exuRhs ru | rv <- recs, ru <- exrRules rv ])
                      checkInductive (lsMutUniv st) (lsEnv st) types ctors recs
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
    when warming warmLicences
    sort <- inferSortOf ty
    unless (lsDefer st) $ checkType val ty
    -- Asked in the same run as the check, so it reuses its memo tables; asked
    -- of the /statement/, so it costs a head normalisation and nothing more.
    -- Which is also why deferring the value check does not disturb it, and so
    -- does not disturb which constants the environment ends up holding.
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
  pure st { lsEnv = env', lsObs = obs
          , lsSeen = lsSeen st + 1
          , lsWarmAt = if warming then max 1 (2 * lsWarmAt st) else lsWarmAt st }
  where
    -- The environment the obligation reads is the one this declaration was
    -- admitted in, and not the one it is admitted into: a value may not mention
    -- the constant it is defining, which is the whole of the termination
    -- argument for a @def@.
    obs | lsDefer st = Obligation n (label (runTC (lsEnv st) lps (checkType val ty)))
                         : lsObs st
        | otherwise  = lsObs st
    -- 'step' does this for the checks it runs itself; an obligation outlives it.
    label = either (Left . ((showName n ++ ": ") ++)) Right
    -- Only when the value checks are deferred: without that the licences travel
    -- as they always have, and the default path is left exactly as it was.
    warming = lsDefer st && lsSeen st >= lsWarmAt st

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
    bad = S.unions (map (constsMeeting (envUnsafe env)) es)

commas :: [String] -> String
commas = foldr1 (\a b -> a ++ ", " ++ b)

-- Inductive declarations ----------------------------------------------------------

checkInductive :: Bool -> Env -> [ExInd] -> [ExCtor] -> [ExRec] -> Either String Env
checkInductive _ _ [] _ _ = Left "inductive declaration with no types"
checkInductive mutUniv env types ctors recs = do
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
      -- One private namespace for the whole block: the specialised containers
      -- of §9.1 and, if the block is flattened, the two types of §9.3 all hang
      -- off it.  Taking it here and using @env'@ from now on is what carries
      -- the bump into the environment this declaration returns.
      let (privRoot, env') = freshPriv env
      (declCtorTys, nested) <- runTC env' lvls $
        planNesting (exiNumNested iv0) nps lvls paramTele declNames privRoot
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

      -- Two ways to admit the block, and only one of them hands
      -- "Kernel.Inductive" a block the file wrote.  A block that is already a
      -- single inductive type goes straight through; every other shape -- more
      -- than one declared type, or a nesting whose compilation just added a
      -- member -- is flattened first, and what the core sees is the two single
      -- types the flattening built (SPEC.md §9.3).  So no mutual block reaches
      -- the core.  Both paths come back having admitted every constant the
      -- file declared and having compared every exported recursor against the
      -- one they derived; what is left over is the bookkeeping below, which is
      -- the same either way.
      -- A block whose types do not all land in the same universe is one no
      -- other Lean kernel will look at, and the flattening below assumes they
      -- do (SPEC.md §8.3 is what enforces it: the members become one type, so
      -- they had better have one sort).  It is nonetheless a block the type
      -- theory has, and "Front.Hetero" derives it from ones that are already
      -- admissible; --enforce-mutual-univ turns that off and mirrors everyone
      -- else.  Reading the members' sorts is only worth doing for a block that
      -- has more than one, and a block whose sorts cannot even be read is left
      -- to the paths below to reject with their own message.
      let resLvls = case resultLevels env' "inductive: " lvls nps paramTele
                           (declMembers ++ auxMembers) of
                      Right ls -> ls
                      Left _   -> []
          hetero  = nDecl + length nested > 1 && case resLvls of
                      (l : ls) -> not (all (levelEquiv l) ls)
                      []       -> False
      br <- if hetero
              then do
                when mutUniv $
                  Left "the types of a mutual inductive block must all land in \
                       \the same universe (--enforce-mutual-univ)"
                unless (null nested) $
                  Left "a mutual inductive block whose types land in different \
                       \universes may not also have nested occurrences"
                heteroBlock env' groups declMembers resLvls paramTele lvls nps
                            recs privRoot
              else if nDecl + length nested > 1
                then flattenBlock env' groups declMembers auxMembers nested
                                  paramTele nDecl lvls nps recs privRoot
                else singleBlock env' groups declMembers lvls nps recs

      -- The export's own bookkeeping must agree with what we derived.
      forM_ (zip3 types (brIndices br) (brFields br)) $ \(iv, nIdx, nFields) -> do
        unless (exiNumIndices iv == nIdx) $
          Left (showName (exiName iv) ++ " declares " ++ show (exiNumIndices iv)
                ++ " indices, but its type has " ++ show nIdx)
        derivedFlag "isRec" (exiName iv) (exiIsRec iv) (brRec br)
        derivedFlag "isReflexive" (exiName iv) (exiIsReflexive iv) (brRefl br)
        forM_ (zip3 [0 ..] (exiCtors iv) nFields) $ \(k, cn, nf) -> do
          c <- findCtor cn
          unless (excInduct c == exiName iv) $ Left "constructor of the wrong type"
          unless (excLevels c == lvls) $
            Left "constructor has different universe parameters from its type"
          unless (excIdx c == k) $
            Left ("constructor " ++ showName cn ++ " has the wrong index")
          unless (excNumParams c == nps) $
            Left ("constructor " ++ showName cn ++ " has the wrong numParams")
          unless (excNumFields c == nf) $
            Left ("constructor " ++ showName cn ++ " declares "
                  ++ show (excNumFields c) ++ " fields but has " ++ show nf)
      pure (brEnv br)
  where
    findCtor n = case find ((== n) . excName) ctors of
      Just c  -> Right c
      Nothing -> Left ("no exported constructor named " ++ showName n)


-- | Admit a block of more than one type by flattening it (SPEC.md §9.3).
flattenBlock :: Env -> [[ExCtor]] -> [CoreMember] -> [CoreMember] -> [Nested]
             -> [(Binder, Expr)] -> Int -> [Name] -> Int -> [ExRec] -> Name
             -> Either String BlockResult
flattenBlock env0 groups declMembers auxMembers nested paramTele nDecl
             lvls nps recs privRoot = do
  let members   = declMembers ++ auxMembers
      declNames = map cmName declMembers
      ctxt      = "flattening the block of " ++ showName (head declNames) ++ ": "
      unnest | null nested = id
             | otherwise   = applyAux lvls nps nested
  cb <- flattenCore env0 ctxt (unAux nested) members paramTele lvls nps
                    (elimHint (map exrLevels recs) lvls) privRoot

  -- The nesting compilation of §9.1 stands between the type the block gives a
  -- constructor and the type the file wrote; it is undone by 'applyAux'.  Only
  -- the declared members are asked: an auxiliary's constructors are not in the
  -- file to compare against.
  forM_ (zip (concat groups)
             (concat (map (map snd . cmCtors) declMembers))) $ \(c, cty) ->
    either (\e -> Left (ctxt ++ "constructor " ++ showName (excName c)
                        ++ ": " ++ e)) (const (Right ())) $
      runTC (cbScratch cb) lvls $ do
        ok <- isDefEq (excType c) (unnest cty)
        unless ok $ throwTC ("the block does not give it the type it declares\
          \\n  declared " ++ showExpr (excType c)
          ++ "\n  derived  " ++ showExpr (unnest cty))

  -- Put the real containers back where §9.1 put auxiliaries, and check that no
  -- auxiliary is left anywhere in what the caller will get.
  let ourRs = [ r { recType   = unnest (recType r)
                  , recInduct = unAux nested (recInduct r)
                  , recRules  = [ ru { rrCtor = unAux nested (rrCtor ru)
                                     , rrRhs  = unnest (rrRhs ru) }
                                | ru <- recRules r ]
                  }
              | r <- cbRecs cb ]
      invented = map nsAux nested ++ [ i | n <- nested, (i, _) <- nsCtorMap n ]
  forM_ ourRs $ \r ->
    case [ n | n <- invented
             , any (occursConst n) (recType r : map rrRhs (recRules r)) ] of
      []      -> Right ()
      (n : _) -> Left (ctxt ++ "internal: " ++ showName n ++ " survives in the \
                       \derived recursor " ++ showName (recName r))

  -- And so the block's own constants, on the environment we were handed:
  -- nothing the flattening invented ever reaches it.
  let ourInds = take nDecl (cbInds cb)
      ourCs = [ [ ci { ctorType = excType c } | (ci, c) <- zip cis g ]
              | (g, cis) <- zip groups (take nDecl (cbCtors cb)) ]
  envInd <- foldM addConst env0
    (map CInd ourInds ++ map CCtor (concat ourCs) ++ map CRec ourRs)
  forM_ ourRs $ \r -> do
    either (\e -> Left ("recursor " ++ showName (recName r)
                        ++ " does not typecheck after flattening: " ++ e))
           (const (Right ()))
           (runTC envInd (recLevels r) (inferSortOf (recType r)))
    checkRecRules envInd r
  forM_ ourRs $ \r -> case find ((== recName r) . exrName) recs of
    Nothing -> Left ("no exported recursor named " ++ showName (recName r))
    Just rv -> checkRecursorMatches envInd declNames rv r

  pure BlockResult
    { brEnv     = envInd
    , brIndices = take nDecl (cbNumIdx cb)
    , brFields  = map (map ctorNumFields) ourCs
    , brRec     = cbRec cb
    , brRefl    = cbRefl cb
    }


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
planNesting :: Int -> Int -> [Name] -> [(Binder, Expr)] -> [Name] -> Name
            -> [Expr] -> TC ([Expr], [Nested])
planNesting cap nps lvls paramTele declNames privRoot declCtorTys =
  withLocals paramTele $ \ps -> do
    env <- getEnv
    opened <- mapM (instParams nps (map FVar ps)) declCtorTys
    found  <- discover env [] opened
    if null found then pure (declCtorTys, []) else do
      let auxNames = [ mkNum (mkStr privRoot (B.pack "nested")) i
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

-- | A @quot@ line, read but not yet admitted.
-- | A @quot@ line, read but not yet admitted, and why it is still waiting.
data QuotD = QuotD !QuotKind !Name ![Name] !Expr String

-- | Why a queued primitive did not go through the last time it was tried.
qdWhy :: QuotD -> String
qdWhy (QuotD _ n _ _ why) = showName n ++ ": " ++ why

-- | Admit every queued quotient primitive that will now go through, repeating
-- while any of them does.
--
-- Each primitive's expected type is stated in terms of the others -- @Quot.mk@
-- lands in the quotient type, @Quot.ind@ quantifies over the class map -- so a
-- file that declares them out of order has, at the moment a line is read,
-- nothing to state that line's expected type against.  Rather than fix an
-- order the format does not fix, a line that cannot be stated yet is held and
-- retried when the next one arrives.  Nothing is weakened: every primitive is
-- checked against the same expected type in the end, and 'checkQuotPackage'
-- still requires the package to be complete.
--
-- The retry loop terminates because each round either admits at least one
-- primitive or stops, and a file has finitely many.
quotFlush :: LS -> LS
quotFlush st = case onePass (lsQuotPend st) st { lsQuotPend = [] } of
    (st', True)  -> quotFlush st'
    (st', False) -> st'
  where
    onePass [] acc = (acc, False)
    onePass (q@(QuotD kind n lps ty _) : qs) acc = case admitQuot acc q of
      Right acc' -> (fst (onePass qs acc'), True)
      Left why   -> onePass qs acc { lsQuotPend = lsQuotPend acc
                                                    ++ [QuotD kind n lps ty why] }

-- | Check one quotient primitive against the type its kind demands, and enter
-- it.  The error is what 'quotFlush' reads as \"not yet\", and what the end of
-- the file reports if it never becomes \"yes\".
admitQuot :: LS -> QuotD -> Either String LS
admitQuot st (QuotD kind n lps ty _) = do
  run (inferSortOf ty)
  when (kind == QLift) $ checkEqShape (lsEnv st)
  expected <- expectedQuot st kind n lps
  run $ do
    ok <- isDefEq ty expected
    unless ok $ throwTC ("quotient primitive has the wrong type\n  declared "
                         ++ showExpr ty ++ "\n  expected " ++ showExpr expected)
  env' <- addConst (lsEnv st) (CQuot n lps ty kind)
  pure st { lsEnv    = env' { envQuotInit = True }
          , lsQuotTy = if kind == QType then Just n else lsQuotTy st
          , lsQuotMk = if kind == QCtor then Just n else lsQuotMk st
          , lsQuots  = (kind, n) : lsQuots st }
  where
    run act = either Left (const (Right ())) (runTC (lsEnv st) lps act)

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
