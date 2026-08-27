{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE LambdaCase #-}

-- | Deriving one inductive block.
--
-- Between "Front.Lower", which reads a block off the file, and
-- "Kernel.Inductive", which admits a single non-mutual type, sits the question
-- of how a block of several types becomes several single types.  This module
-- is the answer, and everything that has more than one caller.
--
-- 'flattenCore' is the derivation of SPEC.md §9.3: build one flat type indexed
-- by a tag, admit /that/, and read the block's constants back off it.
-- "Front.Lower" runs it on the block the file wrote; "Front.Hetero" runs it on
-- blocks the file did not write, on its way to the same place.
module Front.Block
  ( -- * What a derivation produces
    BlockResult (..)
  , CoreBlock (..)
    -- * The members of a block
  , CoreMember (..)
  , coreOf
  , elimHint
    -- * Deriving
  , flattenCore
  , singleBlock
    -- * Checking a derivation against the file
  , checkRecRules
  , checkRecursorMatches
  , derivedFlag
    -- * Small shared pieces
  , checkLevelParams
  , instLams
  , instParams
  , openArity
  , regroup
  , withFields
  ) where

import           Control.Monad  (foldM, forM, forM_, unless, when)
import qualified Data.ByteString.Char8 as B
import           Data.List      (elemIndex, find, nub)
import           Front.Export
import           Kernel.Check
import           Kernel.Env
import           Kernel.Expr
import           Kernel.Inductive
import           Kernel.Level
import           Kernel.Name

-- | A declaration may not bind the same universe parameter twice.
checkLevelParams :: [Name] -> Either String ()
checkLevelParams lps
  | length (nub lps) == length lps = Right ()
  | otherwise = Left "duplicate universe parameter"

-- | Peel @k@ leading @Pi@ binders, substituting the given arguments.
instParams :: Int -> [Expr] -> Expr -> TC Expr
instParams 0 _ ty = pure ty
instParams k (a : as) ty = do
  (_, cod) <- ensurePi ty
  instParams (k - 1) as (inst1 a cod)
instParams _ [] _ = throwTC "nested inductive: not enough parameter arguments"

-- | Cut a flat list back into the given group sizes.
regroup :: [Int] -> [a] -> [[a]]
regroup []       _  = []
regroup (k : ks) xs = let (a, b) = splitAt k xs in a : regroup ks b

-- | What admitting a block leaves for 'checkInductive' to compare against the
-- export's informational fields.  Everything else -- the constants, the derived
-- recursors and their comparison -- is already done and in 'brEnv'.
data BlockResult = BlockResult
  { brEnv     :: !Env
  , brIndices :: ![Int]     -- ^ index count of each declared member
  , brFields  :: ![[Int]]   -- ^ field count of each declared constructor
  , brRec     :: !Bool      -- ^ some constructor of the block is recursive
  , brRefl    :: !Bool      -- ^ ... under a binder
  }

-- | Reuse the export's name for the fresh elimination universe when it has one,
-- so that the derived recursor type is literally the same term.
elimHint :: [[Name]] -> [Name] -> Name
elimHint recLpss indLps = case [ h | (h : t) <- recLpss
                                   , length t == length indLps ] of
  (h : _) -> h
  _       -> str "u"

-- | One member of a block, before the block is compiled away.
--
-- The core has no notion of a block any more (SPEC.md §9.3), so this is the
-- front end's own bookkeeping: everything §9.1 and §9.3 need to know about a
-- family they are on their way to handing over as a 'CoreInd'.
data CoreMember = CoreMember
  { cmName    :: !Name
  , cmArity   :: !Expr             -- ^ @forall params indices, Sort l@
  , cmCtors   :: ![(Name, Expr)]   -- ^ in constructor-index order
  , cmRecName :: !Name
  }

-- | Hand one member to the core.
coreOf :: [Name] -> Int -> Name -> CoreMember -> CoreInd
coreOf lvls nps hint m = CoreInd
  { coreLevels    = lvls
  , coreNumParams = nps
  , coreName      = cmName m
  , coreArity     = cmArity m
  , coreCtors     = cmCtors m
  , coreRecName   = cmRecName m
  , coreElimHint  = hint
  }

-- | Admit a block that is already a single inductive type with no nesting:
-- hand it to "Kernel.Inductive" as it stands.
--
-- This is the only place the core is asked to admit a type the file wrote as
-- the file wrote it.  Everything else goes through 'flattenBlock', which calls
-- the core twice, each time on a type it built itself.
singleBlock :: Env -> [[ExCtor]] -> [CoreMember] -> [Name] -> Int -> [ExRec]
            -> Either String BlockResult
singleBlock env groups declMembers lvls nps recs = do
      m <- case declMembers of
        [x] -> Right x
        _   -> Left "internal: a single-type block with more than one member"
      ai <- admitInd env (coreOf lvls nps (elimHint (map exrLevels recs) lvls) m)
      let ind = aiInd ai
          r   = aiRec ai
          ourCs = [ ci { ctorType = excType c }
                  | (ci, c) <- zip (aiCtors ai) (concat groups) ]
      envInd <- foldM addConst env
        (CInd ind : map CCtor ourCs ++ [CRec r])
      checkRecRules envInd r
      case find ((== recName r) . exrName) recs of
        Nothing -> Left ("no exported recursor named " ++ showName (recName r))
        Just rv -> checkRecursorMatches envInd [indName ind] rv r
      pure BlockResult
        { brEnv     = envInd
        , brIndices = [indNumIndices ind]
        , brFields  = [map ctorNumFields ourCs]
        , brRec     = indIsRecursive ind
        , brRefl    = aiReflexive ai
        }

-- | A boolean the export restates that the kernel also derives.
--
-- @isRec@ and @isReflexive@ are, in the format's own words, \"informational
-- fields\" the elaborator computed; no rule in this kernel reads them off the
-- file.  They are still checked, for the reason every other redundant field is
-- (SPEC.md §1): a number or flag the export supplies and nobody verifies is a
-- place where a file can say one thing and mean another, and the cost of
-- closing it is one comparison.
--
-- Both flags are read as describing the /block/, not the member: a mutual
-- block is one declaration, and a member with no recursive field of its own
-- still has a recursor that recurses, because the block's recursors call each
-- other.  So @and@-ing the members' own answers would leave the flag saying
-- something no rule of the theory means, and a member of a recursive block is
-- reported recursive.
derivedFlag :: String -> Name -> Bool -> Bool -> Either String ()
derivedFlag what n declared derived
  | declared == derived = Right ()
  | declared            = bad "false"
  | otherwise           = bad "true"
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
    -- Positionally: the rules of a recursor are in constructor order, which is
    -- the order the constructors were declared in.  Matching them by name
    -- instead would let a file permute them, and a permuted list is a file
    -- saying one thing and meaning another (SPEC.md §12.9) -- and, with a
    -- repeated name, a list that leaves some constructor with no rule at all
    -- while still having the right length.
    forM_ (zip (exrRules rv) (recRules r)) $ \(ru, our) -> do
        unless (exuCtor ru == rrCtor our) $
          throwTC ("the reduction rules are for " ++ showName (exuCtor ru)
                   ++ " where constructor order puts " ++ showName (rrCtor our))
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

-- | Typecheck a recursor's reduction rules: for each one, the right-hand side
-- must have the type the left-hand side has.
--
-- Every other check on a recursor is a check on its /type/.  §8.7 derives it and
-- typechecks it, §9.3 folds it and typechecks it again, and §8.8 requires the
-- export to declare the same one.  The reduction rules get none of that: they
-- are terms this kernel builds and then believes, and the only thing standing
-- behind them is §8.8's comparison against the rules the export declares --
-- which is a comparison of two untypechecked terms, and says nothing at all if
-- both were built the same wrong way.
--
-- Nothing about the construction makes this superfluous.  A recursor whose rule
-- is ill-typed at the type its own left-hand side has is a recursor whose iota
-- rule does not preserve typing, and a kernel that admits one is unsound
-- whatever else it checked.  So: reconstruct the left-hand side from the
-- constructor, infer its type, and check the right-hand side against it.
--
-- The constructor is not necessarily the one the block declared.  §9.1's
-- unnesting replaces an auxiliary's constructors by the real container's, so an
-- auxiliary recursor's rules are for @List.cons@ and not for a constructor of
-- the block -- with @List@'s parameters, not the block's.  So the parameters
-- are read off the major premise's own type rather than assumed to be the
-- recursor's, which is also what makes this a real check on the transport:
-- §9.1 asserts that the specialised copy may be retyped at the container, and
-- here that assertion has to typecheck.
checkRecRules :: Env -> RecInfo -> Either String ()
checkRecRules env r =
  either (\e -> Left ("the reduction rules of " ++ showName (recName r)
                      ++ " do not typecheck: " ++ e))
         (const (Right ())) $
  runTC env (recLevels r) $ do
    let us   = map LParam (recLevels r)
        npre = recNumParams r + recNumMotives r + recNumMinors r
        (tele, _) = unPisN (npre + recNumIndices r + 1) (recType r)
    unless (length tele == npre + recNumIndices r + 1) $
      throwTC "internal: its type does not have the telescope it says it has"
    withLocals tele $ \xs -> do
      let preArgs = map FVar (take npre xs)
      majTy <- whnf =<< localType (last xs)
      (ind, indUs, indArgs) <- case unApps majTy of
        (Const c cus, as) -> getEnv >>= \e' -> case lookupConst e' c of
          Just (CInd i) -> pure (i, cus, as)
          _ -> throwTC ("internal: the major premise is not of an inductive type, \
                        \but of " ++ showExpr majTy)
        _ -> throwTC ("internal: the major premise has no head constant, its type \
                      \is " ++ showExpr majTy)
      let realPs = take (indNumParams ind) indArgs
      forM_ (recRules r) $ \ru -> do
        ci <- getEnv >>= \e' -> case lookupConst e' (rrCtor ru) of
          Just (CCtor c) -> pure c
          _ -> throwTC (showName (rrCtor ru) ++ " is not a constructor")
        unless (ctorInduct ci == indName ind) $
          throwTC (showName (rrCtor ru) ++ " is not a constructor of "
                   ++ showName (indName ind))
        unless (ctorNumFields ci == rrNumFields ru) $
          throwTC ("the rule for " ++ showName (rrCtor ru) ++ " claims "
                   ++ show (rrNumFields ru) ++ " fields, but the constructor has "
                   ++ show (ctorNumFields ci))
        cty <- instParams (indNumParams ind) realPs
                 (instLevelsE (ctorLevels ci) indUs (ctorType ci))
        withLocals (fst (unPisN (rrNumFields ru) cty)) $ \bs -> do
          let major = mkApps (Const (rrCtor ru) indUs) (realPs ++ map FVar bs)
          mty <- whnf =<< infer major
          let ixs = drop (indNumParams ind) (snd (unApps mty))
          unless (length ixs == recNumIndices r) $
            throwTC ("applying " ++ showName (rrCtor ru) ++ " gives "
                     ++ show (length ixs) ++ " indices, expected "
                     ++ show (recNumIndices r))
          want <- infer (mkApps (Const (recName r) us)
                                    (preArgs ++ ixs ++ [major]))
          checkType (instLams (preArgs ++ map FVar bs) (rrRhs ru)) want

-- Flattening a mutual block ------------------------------------------------------------
--
-- SPEC.md §9.3.  A block of @n@ mutually recursive families
--
-- > T_1 : forall p::pi, alpha_1, Sort l    ...    T_n : forall p::pi, alpha_n, Sort l
--
-- -- whose members are the file's own /and/ the auxiliaries the nesting
-- compilation of §9.1 added -- is derived from two ordinary single inductive
-- types.  The first is a tag type, one constructor per member, carrying that
-- member's indices:
--
-- > Idx     : forall p::pi, Sort v          v = max 1 (sorts of every index)
-- > Idx.mk_j : forall p::pi, a::alpha_j, Idx p
--
-- and the second is the block itself, re-indexed by the tag:
--
-- > F : forall p::pi, Idx p -> Sort l
--
-- whose constructors are the file's own, with every occurrence @T_j p a@
-- rewritten to @F p (Idx.mk_j p a)@.  Those two are the only blocks
-- "Kernel.Inductive" is ever handed, and both have exactly one member: after
-- this pass the core never sees a mutual block at all.
--
-- The block's own constants are then read back off @F@.  Its members and
-- constructors are the ones the file declared, at the types the file gave
-- them; its recursors are @F@'s single recursor, /rewritten/ rather than
-- wrapped.  Writing @bigC = Idx.rec (fun i => F p i -> Sort u) C_1 ... C_n@ for
-- the term that turns the block's @n@ motives into the one motive @F@ has, the
-- rewrite is three iota steps performed by hand:
--
-- > F p (Idx.mk_j p a)              ~>  T_j p a
-- > bigC (Idx.mk_j p a) t           ~>  C_j a t
-- > F.rec p bigC e (Idx.mk_j p a) t ~>  T_j.rec p C e a t
--
-- Every tag in a term @F@'s admission produced is a literal @Idx.mk_j@ -- the
-- rewrite that built @F@'s constructors put it there -- so all three fire
-- everywhere they have to, and what comes back mentions neither @Idx@ nor @F@
-- nor their recursors.  That is checked, not hoped for: 'flattenBlock' refuses
-- the block if any invented name survives in a derived type or reduction rule.
--
-- So @Idx@ and @F@ live and die inside 'flattenBlock'.  They are admitted into
-- a scratch environment that is thrown away, and the environment the caller
-- gets back is @env0@ plus exactly the constants the file declared -- the same
-- shape 'singleBlock' produces, with the members real inductive types (so §5.3
-- projections and §7.2 eta see them) and the recursors primitives (so §9.1's
-- unnesting substitution can reach into their types and rules, which it could
-- not if they were definitions with bodies to preserve).
--
-- Keeping them instead, and letting the members be definitions over @F@, is a
-- shorter construction that deletes the fold; SPEC.md §9.5 records why it does
-- not work, and what it costs to make it work.
--
-- Why this is the same theory and not a larger one:
--
-- * The rewrite that builds @F@ is a bijection on occurrences, so the
--   constructor judgement (§8.4) -- strict positivity and @imax(l',l) <= l@ --
--   is asked exactly the questions it was asked before, and @F@'s recursor is
--   the block's recursors packed into one.
-- * The uniform-universe rule of §8.3 is not assumed here, it is /derived/:
--   @F@ lands in whatever sort the first member does, and @T_j@'s stand-in
--   @fun p a => F p (Idx.mk_j p a)@ typechecks at the arity the file declared
--   only if the @j@-th member lands there too.  A block whose members disagree
--   is rejected by the ordinary rule for definitions.  This is the one place
--   the fork is stricter than the core it replaces: §8.3 exempts the
--   auxiliaries of a nested block from that rule, and here they pay it.
-- * Elimination is decided by §8.5 case 1 alone -- @isDefinitelyNonZero l@ --
--   which is what that rule says for a block of two or more members anyway.
--   @F@ is one type and so can qualify under case 2 where the block would not;
--   the recursors are built at the block's licence, not at @F@'s, so nothing
--   escapes.
-- * The derived recursor types are audited again in the final environment,
--   for the reason §9.1's unnesting is: they were rebuilt behind the kernel's
--   back, so nothing has typechecked them where they will be used.

-- | The constants one flattening invents.
data FlatNames = FlatNames
  { fnIdx     :: !Name           -- ^ the tag type
  , fnIdxCtor :: !(Int -> Name)  -- ^ its @j@-th constructor
  , fnIdxRec  :: !Name
  , fnTy      :: !Name           -- ^ the flat type
  , fnTyRec   :: !Name
  , fnAll     :: ![Name]         -- ^ all of the above, for the step 7 audit
  }

-- | Names in the block's private namespace (see 'Kernel.Env.freshPriv').
--
-- These have to be free -- of every constant the file declares, and of every
-- name the front end has already invented -- because step 7 below rejects a
-- derived term that still mentions one, and that audit is only meaningful if
-- the name could not have got there from the file.  Being rooted at a 'Priv'
-- is what makes them free, with no search and no appeal to what is in the
-- environment at the time.
flatNames :: Name -> Int -> FlatNames
flatNames privRoot nMem = FlatNames
  { fnIdx     = idx
  , fnIdxCtor = tag
  , fnIdxRec  = mkStr idx (B.pack "rec")
  , fnTy      = ty
  , fnTyRec   = mkStr ty (B.pack "rec")
  , fnAll     = [ idx, mkStr idx (B.pack "rec"), ty, mkStr ty (B.pack "rec") ]
                ++ map tag [0 .. nMem - 1]
  }
  where
    idx   = mkStr privRoot (B.pack "idx")
    ty    = mkStr privRoot (B.pack "ty")
    tag k = mkNum (mkStr idx (B.pack "mk")) (toInteger k)

-- | What one flattening derives, before any of it is compared against a file.
--
-- 'flattenBlock' is one caller; the heterogeneous lowering below is the other,
-- and it needs the same machinery pointed at blocks the file never wrote (an
-- all-@Prop@ shadow of the block, and each strongly connected component of its
-- data members on its own).
data CoreBlock = CoreBlock
  { cbNumIdx  :: ![Int]          -- ^ index count of each member
  , cbInds    :: ![IndInfo]      -- ^ each member, at the arity it declares
  , cbCtors   :: ![[CtorInfo]]   -- ^ each member's constructors, at its own types
  , cbRecs    :: ![RecInfo]      -- ^ each member's recursor
  , cbRefl    :: !Bool           -- ^ some constructor recurses under a binder
  , cbRec     :: !Bool           -- ^ some constructor of the /block/ recurses
  , cbScratch :: !Env
    -- ^ the environment the flattening worked in: @Idx@, @F@, and the members
    -- as stand-in definitions over @F@.  Only for stating comparisons about the
    -- block that have to see through the flattening; it is not what the caller
    -- should be admitting anything into.
  }

-- | Derive a block by flattening it: see the note above.
--
-- @disp@ renames a member for an error message (§9.1's auxiliaries are reported
-- as the container they stand for), and @hint@ is the preferred name for the
-- fresh elimination universe.
flattenCore :: Env -> String -> (Name -> Name) -> [CoreMember] -> [(Binder, Expr)]
            -> [Name] -> Int -> Name -> Name -> Either String CoreBlock
flattenCore env0 _ _ [m] _ lvls nps hint _ = do
  ai <- admitInd env0 (coreOf lvls nps hint m)
  envS <- foldM addConst env0
    (CInd (aiInd ai) : map CCtor (aiCtors ai) ++ [CRec (aiRec ai)])
  pure CoreBlock
    { cbNumIdx  = [indNumIndices (aiInd ai)]
    , cbInds    = [aiInd ai]
    , cbCtors   = [aiCtors ai]
    , cbRecs    = [aiRec ai]
    , cbRefl    = aiReflexive ai
    , cbRec     = indIsRecursive (aiInd ai)
    , cbScratch = envS
    }
flattenCore env0 ctxt disp members paramTele lvls nps hint privRoot = do
  let memNames  = map cmName members
      nMem      = length members
      nCtors    = map (length . cmCtors) members
      selfL     = map LParam lvls
      fn        = flatNames privRoot nMem
      ctorCtxt cn = ctxt ++ "constructor " ++ showName cn ++ ": "

  -- 1. Each member's index telescope, the sort it lands in, and the sorts its
  --    indices live in.  An arity may not mention the block -- the core checks
  --    them in the incoming environment too -- so all of this is readable here.
  info <- runTC env0 lvls $ withLocals paramTele $ \ps ->
    forM members $ \m -> do
      _ <- inferSortOf (cmArity m)
      (is, l) <- openArity ctxt nps ps (cmArity m)
      ss <- forM is $ \x -> localType x >>= inferSortOf
      pure (length is, l, ss)
  let nIdxs  = [ k | (k, _, _) <- info ]
      resLvl = case info of ((_, l, _) : _) -> l; [] -> LZero
      tagLvl = foldr mkMax (mkSucc LZero) (concat [ ss | (_, _, ss) <- info ])

  -- 2. The tag type.  Its universe dominates every index's, so the constructor
  --    judgement passes; and it is a successor, so 'decideLargeElim' grants it
  --    elimination into every sort, which is what step 6 needs.
  idxDecl <- runTC env0 lvls $ withLocals paramTele $ \ps -> do
    ar <- closePis ps (Sort tagLvl)
    cs <- forM (zip [0 ..] members) $ \(k, m) -> do
      (is, _) <- openArity ctxt nps ps (cmArity m)
      t <- closePis (ps ++ is) (mkApps (Const (fnIdx fn) selfL) (map FVar ps))
      pure (fnIdxCtor fn k, t)
    pure CoreMember { cmName = fnIdx fn, cmArity = ar, cmCtors = cs
                    , cmRecName = fnIdxRec fn }
  aiIdx <- admitInd env0 (coreOf lvls nps (str "u") idxDecl)
  -- 'idxRecUs' below assumes this shape: a fresh elimination universe, then the
  -- block's own.  It holds because 'tagLvl' is a successor.
  unless (length (recLevels (aiRec aiIdx)) == 1 + length lvls) $
    Left (ctxt ++ "internal: the tag type does not eliminate into every sort")
  envIdx <- foldM addConst env0
    (CInd (aiInd aiIdx) : map CCtor (aiCtors aiIdx) ++ [CRec (aiRec aiIdx)])

  -- 3. The flat type, and the block's own constructors re-headed at it.
  (flatCtorTys, flatDecl) <- runTC envIdx lvls $ withLocals paramTele $ \ps -> do
    let rw = flatRewrite memNames selfL fn nIdxs nps (map FVar ps)
    ar <- closePis ps (mkArrow (mkApps (Const (fnIdx fn) selfL) (map FVar ps))
                               (Sort resLvl))
    cs <- forM members $ \m ->
      forM (cmCtors m) $ \(cn, cty) -> do
        body <- rw <$> peelSharedParams (ctorCtxt cn) nps ps cty
        forM_ memNames $ \n -> when (occursConst n body) $
          throwTC (ctorCtxt cn ++ showName n ++ " occurs somewhere the flattening \
            \cannot follow it; every occurrence of a member of a mutual block must \
            \be applied to the block's own parameters and to all of that member's \
            \indices")
        t <- closePis ps body
        pure (cn, t)
    pure (cs, CoreMember { cmName = fnTy fn, cmArity = ar
                         , cmCtors = concat cs, cmRecName = fnTyRec fn })
  aiF <- admitInd envIdx (coreOf lvls nps hint flatDecl)
  let indF   = aiInd aiF
      ctorFs = aiCtors aiF
      recF   = aiRec aiF
  envF <- foldM addConst envIdx [CInd indF, CRec recF]

  -- 4. Each member stands in as @fun p a => F p (Idx.mk_j p a)@ for as long as
  --    it takes to state the two comparisons below.  This is where §8.3 is paid
  --    for: a member that does not land in the sort the first one does fails to
  --    typecheck here.
  vals <- runTC envF lvls $ withLocals paramTele $ \ps ->
    forM (zip [0 ..] members) $ \(k, m) -> do
      (is, _) <- openArity ctxt nps ps (cmArity m)
      closeLams (ps ++ is) (mkApps (Const (fnTy fn) selfL)
        (map FVar ps ++ [ mkApps (Const (fnIdxCtor fn k) selfL)
                                 (map FVar ps ++ map FVar is) ]))
  forM_ (zip members vals) $ \(m, v) ->
    either (\e -> Left (ctxt ++ showName (disp (cmName m))
                        ++ " does not have the type it declares once the block is \
                           \flattened -- which is what it looks like for the members \
                           \of a mutual block to land in different universes: " ++ e))
           (const (Right ()))
           (runTC envF lvls (checkType v (cmArity m)))
  envTy <- foldM addConst envF
    [ CDef DefInfo { defName = cmName m, defLevels = lvls, defType = cmArity m
                   , defValue = v, defHint = HAbbrev }
    | (m, v) <- zip members vals ]

  -- 5. The constructors, at the types the block gives them.  What @F@'s
  --    constructor was admitted at is the flattening of that, so the two are
  --    compared with the stand-ins of step 4 available to unfold.  This is asked
  --    of every member; whether the block's own types are in turn the ones the
  --    /file/ wrote is the caller's question, and 'cbScratch' is handed back so
  --    it can be asked in the same environment.
  forM_ (zip (concat flatCtorTys) (concat (map (map snd . cmCtors) members))) $
    \((cn, flatTy), cty) ->
      either (\e -> Left (ctorCtxt cn ++ e)) (const (Right ())) $
        runTC envTy lvls $ do
          ok <- isDefEq cty flatTy
          unless ok $ throwTC ("the flattening does not give it the type its \
            \block gives it\n  in the block " ++ showExpr cty
            ++ "\n  flattened  " ++ showExpr flatTy)

  -- 6. The recursors.  The elimination universe is the block's -- §8.5 case 1 --
  --    even when @F@, being a single type, would have been granted more.
  let wantLarge = isDefinitelyNonZero resLvl
      fRecLarge = length (recLevels recF) > length lvls
      wrapLvls  = if wantLarge then recLevels recF else lvls
      elimLvl   = if wantLarge then LParam (head (recLevels recF)) else LZero
      fRecUs    = [ elimLvl | fRecLarge ] ++ selfL
      idxRecUs  = mkIMax resLvl (mkSucc elimLvl) : selfL
      nMinors   = recNumMinors recF
      recNames  = map cmRecName members
      wrapUs    = map LParam wrapLvls

      -- The three iota steps of the note above, run by hand over a term the
      -- core built out of @Idx@ and @F@.  'ps', 'cVars' and 'es' are the locals
      -- the term is stated over: matching against them is what makes each step
      -- fire only on an occurrence in the shape it was put there in.
      unflatten ps cVars bigC eArgs = go
        where
          pArgs = map FVar ps
          cArgs = map FVar cVars
          -- @Idx.mk_j p a@, the only shape a tag ever has in one of these terms.
          asTag t = case unApps t of
            (Const c us, as)
              | Just j <- lookup c tags
              , length us == length selfL, and (zipWith levelEquiv us selfL)
              , length as == nps + nIdxs !! j
              , take nps as == pArgs
              -> Just (j, drop nps as)
            _ -> Nothing
          tags = [ (fnIdxCtor fn j, j) | j <- [0 .. nMem - 1] ]
          go e = case step e of
            Just e' -> go e'
            Nothing -> case unApps e of
              (h, [])   -> descend h
              (h, args) -> mkApps (descend h) (map go args)
          descend e = case e of
            Lam n t b   -> Lam n (go t) (go b)
            Pi  n t b   -> Pi  n (go t) (go b)
            Let n t v b -> Let n (go t) (go v) (go b)
            Proj tn i s -> Proj tn i (go s)
            _           -> e
          step e = case unApps e of
            -- F.rec p bigC e (Idx.mk_j p a) t  ~>  T_j.rec p C e a t
            (Const c us, as)
              | c == fnTyRec fn, us == fRecUs
              , length as >= nps + 1 + nMinors + 2
              , take nps as == pArgs
              , as !! nps == bigC
              , take nMinors (drop (nps + 1) as) == eArgs
              , (maj : t : after) <- drop (nps + 1 + nMinors) as
              , Just (j, ixs) <- asTag maj
              -> Just (mkApps (Const (recNames !! j) wrapUs)
                         (pArgs ++ cArgs ++ eArgs ++ ixs ++ (t : after)))
            -- bigC (Idx.mk_j p a) t  ~>  C_j a t
            (Const c _, as)
              | c == fnIdxRec fn
              , length as >= nps + 1 + nMem + 1
              , take nps as == pArgs
              , take nMem (drop (nps + 1) as) == cArgs
              , (maj : after) <- drop (nps + 1 + nMem) as
              , Just (j, ixs) <- asTag maj
              -> Just (mkApps (FVar (cVars !! j)) (ixs ++ after))
            -- F p (Idx.mk_j p a)  ~>  T_j p a
            (Const c us, as)
              | c == fnTy fn
              , length us == length selfL, and (zipWith levelEquiv us selfL)
              , length as >= nps + 1
              , take nps as == pArgs
              , Just (j, ixs) <- asTag (as !! nps)
              -> Just (mkApps (Const (memNames !! j) selfL)
                         (pArgs ++ ixs ++ drop (nps + 1) as))
            _ -> Nothing

      -- Everything a recursor of the block is quantified over: the parameters,
      -- one motive per member, and the minor premises, which are @F@'s own with
      -- its single motive already instantiated at 'bigC' and folded back.
      withCtx k = withLocals paramTele $ \ps -> do
        kappas <- forM members $ \m -> do
          (is, _) <- openArity ctxt nps ps (cmArity m)
          closePis is (mkArrow (mkApps (Const (cmName m) selfL)
                                       (map FVar ps ++ map FVar is))
                               (Sort elimLvl))
        cVars <- forM (zip [1 :: Integer ..] kappas) $ \(i, t) ->
          freshFVar (Binder (mkNum (str "motive") i)) t
        let tagTy = mkApps (Const (fnIdx fn) selfL) (map FVar ps)
            bigC  = mkApps (Const (fnIdxRec fn) idxRecUs)
              (map FVar ps
               ++ [ Lam (Binder (str "i")) tagTy
                      (mkArrow (mkApps (Const (fnTy fn) selfL)
                                       (map FVar ps ++ [BVar 0]))
                               (Sort elimLvl)) ]
               ++ map FVar cVars)
            rw = unflatten ps cVars bigC
        rest <- peelSharedParams ctxt nps ps
                  (instLevelsE (recLevels recF) fRecUs (recType recF))
        let (_, afterC)  = unPisN 1 rest
            (minors0, _) = unPisN nMinors (inst1 bigC afterC)
        withLocals [ (b, rw [] t) | (b, t) <- minors0 ] $ \es ->
          k ps cVars es bigC (rw (map FVar es))
  unless (fRecLarge || not wantLarge) $
    Left (ctxt ++ "internal: the flat type lost its large elimination")

  derived <- runTC envTy wrapLvls $ withCtx $ \ps cVars es bigC rw ->
    forM (zip3 [0 ..] members (regroup nCtors (recRules recF))) $ \(j, m, rules) -> do
      (is, _) <- openArity ctxt nps ps (cmArity m)
      z <- freshFVar (Binder (str "t"))
             (mkApps (Const (cmName m) selfL) (map FVar ps ++ map FVar is))
      concl <- closePis (is ++ [z])
                 (mkApps (FVar (cVars !! j)) (map FVar is ++ [FVar z]))
      ty <- closePis (ps ++ cVars ++ es) concl
      -- A rule of @F@ is abstracted over the parameters, @F@'s one motive, the
      -- minor premises and the fields; ours over the parameters, the block's
      -- @n@ motives, the same minor premises and the same fields.  Opening the
      -- first at 'bigC' and closing the second over 'cVars' is the whole
      -- difference, once the recursive calls inside have been folded back.
      rs <- forM (zip rules (map snd (cmCtors m))) $ \(ru, cty) ->
        withFields ctxt nps ps cty (rrNumFields ru) $ \bs -> do
          let body = instLams (map FVar ps ++ [bigC] ++ map FVar es ++ map FVar bs)
                              (instLevelsE (recLevels recF) fRecUs (rrRhs ru))
          rhs <- closeLams (ps ++ cVars ++ es ++ bs) (rw body)
          pure ru { rrRhs = rhs }
      pure RecInfo
        { recName       = cmRecName m
        , recLevels     = wrapLvls
        , recType       = ty
        , recInduct     = cmName m
        , recNumParams  = nps
        , recNumMotives = nMem
        , recNumIndices = nIdxs !! j
        , recNumMinors  = nMinors
        , recRules      = rs
        , recK          = False
        }

  -- 7. Check that nothing this pass invented is left anywhere in what the
  --    caller will get.
  forM_ derived $ \r ->
    case [ n | n <- fnAll fn
             , any (occursConst n) (recType r : map rrRhs (recRules r)) ] of
      []      -> Right ()
      (n : _) -> Left (ctxt ++ "internal: " ++ showName n ++ " survives in the \
                       \derived recursor " ++ showName (recName r))

  -- 8. And so the block's own constants.  They are only described here; adding
  --    them to an environment is the caller's business, because only the caller
  --    knows which of them the file is entitled to see.
  --
  --    'indIsRecursive' is a property of the individual member, not of the
  --    block, and @F@ only knows the block's, so it is recomputed here: does a
  --    member of the block occur in one of this member's constructors?  Nothing
  --    that existed before the block was declared can mention a member of it, so
  --    an occurrence that whnf would expose was already there syntactically, and
  --    this can only over-report -- which costs eta during reduction (§6.1) and
  --    nothing else.
  let selfRec m = or [ occursConst n cty | (_, cty) <- cmCtors m, n <- memNames ]
      ourInds =
        [ IndInfo { indName        = cmName m
                  , indLevels      = lvls
                  , indType        = cmArity m
                  , indNumParams   = nps
                  , indNumIndices  = ni
                  , indCtors       = map fst (cmCtors m)
                  , indIsRecursive = selfRec m
                  , indLargeElim   = wantLarge
                  , indK           = False
                  }
        | (m, ni) <- zip members nIdxs ]
      ourCs = [ [ ci { ctorType = cty, ctorInduct = cmName m, ctorIdx = k }
                | (k, ci, (_, cty)) <- zip3 [0 ..] cis (cmCtors m) ]
              | (m, cis) <- zip members (regroup nCtors ctorFs) ]
  pure CoreBlock
    { cbNumIdx  = nIdxs
    , cbInds    = ourInds
    , cbCtors   = ourCs
    , cbRecs    = derived
    , cbRefl    = aiReflexive aiF
    , cbRec     = indIsRecursive indF
    , cbScratch = envTy
    }

-- | Beta-reduce a term's leading lambdas against the given arguments.
--
-- The terms this is used on are recursor right-hand sides, which
-- 'Kernel.Inductive.mkRule' builds as a lambda per parameter, motive, minor
-- premise and field; if one ever has fewer, the application it falls back to
-- is the same term and the fold that follows simply does not fire -- which
-- step 7 turns into a rejection rather than letting it through.
instLams :: [Expr] -> Expr -> Expr
instLams []         e           = e
instLams (a : as)   (Lam _ _ b) = instLams as (inst1 a b)
instLams as         e           = mkApps e as

-- | Rewrite every occurrence of a member of the block into one of the flat type.
--
-- Syntactic, and deliberately so: 'Kernel.Inductive.analyzeCtor' also demands
-- that an occurrence be at the block's own parameters syntactically, so an
-- occurrence this misses is one the core would have rejected -- and the caller
-- checks that none is left.
flatRewrite :: [Name] -> [Level] -> FlatNames -> [Int] -> Int -> [Expr]
            -> Expr -> Expr
flatRewrite declNames selfL fn nIdxs nps pargs = go
  where
    go e = case unApps e of
      (Const c us, args)
        | Just j <- elemIndex c declNames
        , length us == length selfL
        , and (zipWith levelEquiv us selfL)
        , length args >= nps + nIdxs !! j
        , take nps args == pargs
        -> let (idx, extra) = splitAt (nIdxs !! j) (drop nps args)
           in mkApps (Const (fnTy fn) selfL)
                (pargs ++ [ mkApps (Const (fnIdxCtor fn j) selfL)
                                   (pargs ++ map go idx) ]
                       ++ map go extra)
      (h, [])   -> descend h
      (h, args) -> mkApps (descend h) (map go args)
    descend e = case e of
      Lam n t b   -> Lam n (go t) (go b)
      Pi  n t b   -> Pi  n (go t) (go b)
      Let n t v b -> Let n (go t) (go v) (go b)
      Proj tn i s -> Proj tn i (go s)
      _           -> e

-- | Peel an arity's shared parameters against @ps@, then open every remaining
-- binder, and report the sort it ends in.
openArity :: String -> Int -> [Int] -> Expr -> TC ([Int], Level)
openArity ctxt np ps arity = peelSharedParams ctxt np ps arity >>= go []
  where
    go acc ty = whnf ty >>= \case
      Pi n dom cod -> do
        x <- freshFVar n dom
        go (x : acc) (inst1 (FVar x) cod)
      Sort l -> pure (reverse acc, l)
      other  -> throwTC (ctxt ++ "the type of an inductive must end in a sort, got "
                         ++ showExpr other)

-- | Open the first @n@ fields of a constructor type, past its parameters.
withFields :: String -> Int -> [Int] -> Expr -> Int -> ([Int] -> TC a) -> TC a
withFields ctxt np ps cty n k = peelSharedParams ctxt np ps cty >>= go n []
  where
    go 0 acc _  = k (reverse acc)
    go i acc ty = whnf ty >>= \case
      Pi bn dom cod -> do
        x <- freshFVar bn dom
        go (i - 1) (x : acc) (inst1 (FVar x) cod)
      _ -> throwTC (ctxt ++ "a constructor has fewer fields than its rule claims")
