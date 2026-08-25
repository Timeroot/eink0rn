{-# LANGUAGE LambdaCase #-}
-- | Admitting a block of core inductive types, and deriving their recursors.
--
-- \"Core\" means /flat/: a finite set of mutually recursive families over a
-- shared parameter telescope, each a plain telescope of indices ending in a
-- sort.  No nesting -- a family occurring underneath some other type
-- constructor is compiled away by "Front.Lower" before it gets here, into extra
-- members of the very block this module admits.
--
-- The rules below follow Carneiro, /The Type Theory of Lean/ §2.9 -- the @ctor@
-- and @LE@ judgements, the shape of the recursor, and iota -- almost literally,
-- generalised from one family to a block in the way §2.9 describes.  SPEC.md
-- states them again in the notation used there.
--
-- Notation, as in the thesis:
--
-- > t_j : forall a::alpha_j, Sort l_j     the j-th family, parameters in the context
-- > c : forall b::beta, t_j p[b]          a constructor of the j-th family
-- > b_i : forall x::xi_i, t_k pi_i[b,x]   a recursive field, of the k-th family
--
-- Parameters are ordinary context variables here, exactly as in the thesis; the
-- outer @forall params@ is put back on at the very end.  They are shared: every
-- member of a block has the same parameter telescope, and every occurrence of
-- any member anywhere in the block must be at those very parameters.
module Kernel.Inductive
  ( CoreBlock (..)
  , CoreMember (..)
  , AdmittedBlock (..)
  , admitBlock
  ) where

import           Control.Monad (forM, forM_, unless, when)
import           Data.List     (elemIndex, intercalate, nub)
import           Kernel.Check
import           Kernel.Env
import           Kernel.Expr
import           Kernel.Level
import           Kernel.Name

-- | One family of a block, in the shape the core accepts.
data CoreMember = CoreMember
  { cmName    :: !Name
  , cmArity   :: !Expr             -- ^ @forall params indices, Sort l@
  , cmCtors   :: ![(Name, Expr)]   -- ^ in constructor-index order
  , cmRecName :: !Name
  }

-- | A mutual block.  A single inductive type is the one-member case.
data CoreBlock = CoreBlock
  { cbLevels    :: ![Name]
  , cbNumParams :: !Int
  , cbMembers   :: ![CoreMember]   -- ^ non-empty
  , cbNumDeclared :: !Int
    -- ^ how many of 'cbMembers' the file actually declared.  The rest are the
    -- specialised containers the nesting compilation added (SPEC.md §9), which
    -- are exempt from the uniform-universe rule of §8.3: they stand for types
    -- admitted elsewhere, at whatever universe those have.
  , cbElimHint  :: !Name
    -- ^ preferred name for the fresh elimination universe; purely cosmetic, but
    -- reusing the exported one makes the derived recursors compare syntactically.
  }

-- | Parallel to 'cbMembers' throughout.
data AdmittedBlock = AdmittedBlock
  { abInds      :: ![IndInfo]
  , abCtors     :: ![[CtorInfo]]
  , abRecs      :: ![RecInfo]
  , abReflexive :: ![Bool]
    -- ^ some constructor of this member has a recursive field /under a binder/,
    -- as @Acc.intro@'s @forall y, r y x -> Acc r y@ does.  No rule in this
    -- kernel consults it; it is derived so that "Front.Lower" can hold the
    -- export's @isReflexive@ to something.  ('indIsRecursive' plays the same
    -- part for @isRec@, and is on 'IndInfo' because reduction does use it.)
  }

-- | A recursive field @b_i : forall x::xi, t_k pi@.
data RecOcc = RecOcc
  { roMember  :: !Int               -- ^ @k@: which member of the block it lands in
  , roTele    :: ![(Binder, Expr)]  -- ^ @xi@, a closed de Bruijn telescope
  , roIndices :: ![Expr]            -- ^ @pi@, de Bruijn relative to @xi@
  }

-- | One constructor field.
data CField = CField
  { cfVar   :: !Int             -- ^ the local standing for it
  , cfLevel :: !Level           -- ^ the sort its type lives in
  , cfRec   :: !(Maybe RecOcc)  -- ^ 'Nothing' when the field mentions no member
  }

data CtorShape = CtorShape
  { csName   :: !Name
  , csOwner  :: !Int           -- ^ the member this is a constructor of
  , csFields :: ![CField]
  , csResIdx :: ![Expr]        -- ^ @p[b]@, mentioning the field locals
  }

csNumFields :: CtorShape -> Int
csNumFields = length . csFields

-- | Check an inductive block and derive its constructors and recursors.  The
-- environment must not already contain any of the names involved.
admitBlock :: Env -> CoreBlock -> Either String AdmittedBlock
admitBlock env cb = runTC env (cbLevels cb) (admit cb)

admit :: CoreBlock -> TC AdmittedBlock
admit cb = do
  env0 <- getEnv
  let lvls  = cbLevels cb
      selfL = map LParam lvls
      nps   = cbNumParams cb
      ms    = cbMembers cb
      names = map cmName ms
      ctxt  = "inductive " ++ showName (head names) ++ ": "
      memberCtxt m = "inductive " ++ showName (cmName m) ++ ": "

  unless (not (null ms)) $ throwTC "inductive block with no types"
  unless (nps >= 0) $ throwTC (ctxt ++ "negative parameter count")
  unless (length (nub names) == length names) $
    throwTC (ctxt ++ "the block declares the same type twice")

  -- 1. Every declared arity must be a well-formed type, and they must agree on
  --    the shared parameter telescope.  The first member's is taken as
  --    definitive; the rest are checked against it in step 2.
  forM_ ms $ \m -> inferSortOf (cmArity m)
  let (paramTele, _) = unPisN nps (cmArity (head ms))
  unless (length paramTele == nps) $
    throwTC (ctxt ++ "declares " ++ show nps ++ " parameters but its type has "
             ++ show (length paramTele))

  -- 2. Constructors are checked with every member of the block standing for
  --    itself as an opaque constant of exactly its declared arity.
  envSelf <- foldMTC (\e m -> addC e (CAxiom (cmName m) lvls (cmArity m))) env0 ms
  (ps, arities, shapess) <- withEnv envSelf $ withLocals paramTele $ \ps -> do
    ars <- forM ms $ \m -> do
      rest <- peelSharedParams (memberCtxt m) nps ps (cmArity m)
      (is, res) <- peelPis rest
      lvl <- case res of
        Sort l -> pure l
        _      -> throwTC (memberCtxt m ++ "the type must end in a sort, got "
                           ++ showExpr res)
      tele <- teleOf is
      pure (lvl, tele)
    shs <- forM (zip3 [0 ..] ms ars) $ \(j, m, (lvl, _)) ->
      forM (cmCtors m) $ \(cn, cty) ->
        analyzeCtor names selfL ps lvl nps j cn cty
    pure (ps, ars, shs)

  -- 3. Every type the file declared in this block must land in the /same/ sort.
  --    A block is one definition with one set of motives, and its members are
  --    read as one family indexed by the member; letting the members sit at
  --    different universes would make that reading false.  (SPEC.md §8.3.)
  let indLvls   = map fst arities
      idxTeles  = map snd arities
      declLvls  = take (cbNumDeclared cb) indLvls
  unless (and (zipWith levelEquiv declLvls (drop 1 declLvls))) $
    throwTC (ctxt ++ "the types of a mutual block must all land in the same \
                     \universe, but they land in "
             ++ intercalate ", " (map showLevel declLvls))

  -- 4. Derived attributes.  Large elimination and the @k@ flag are properties of
  --    the block as a whole: one set of motives is shared by every member, so
  --    the weakest member decides.
  let largeElim = decideLargeElim (zip indLvls shapess)
      kLike     = case (ms, indLvls, shapess) of
        ([_], [l], [[sh]]) -> isDefinitelyZero l && csNumFields sh == 0
        _                  -> False
      indInfos =
        [ IndInfo { indName        = cmName m
                  , indLevels      = lvls
                  , indType        = cmArity m
                  , indNumParams   = nps
                  , indNumIndices  = length idxTele
                  , indCtors       = map csName shs
                  , indIsRecursive = any (any (isRecField . cfRec) . csFields) shs
                  , indLargeElim   = largeElim
                  , indK           = kLike
                  }
        | (m, idxTele, shs) <- zip3 ms idxTeles shapess ]
      ctorInfoss =
        [ [ CtorInfo { ctorName      = cn
                     , ctorLevels    = lvls
                     , ctorType      = cty
                     , ctorInduct    = cmName m
                     , ctorIdx       = k
                     , ctorNumParams = nps
                     , ctorNumFields = csNumFields sh
                     }
          | (k, (cn, cty), sh) <- zip3 [0 ..] (cmCtors m) shs ]
        | (m, shs) <- zip ms shapess ]

  envFull <- do
    e1 <- foldMTC (\e i -> addC e (CInd i)) env0 indInfos
    foldMTC (\e c -> addC e (CCtor c)) e1 (concat ctorInfoss)

  recInfos <- withEnv envFull $
    buildRecursors cb indInfos ps idxTeles largeElim kLike shapess

  pure (AdmittedBlock indInfos ctorInfoss recInfos
          [ any (any (isReflField . cfRec) . csFields) shs | shs <- shapess ])
  where
    isRecField (Just _) = True
    isRecField Nothing  = False

    isReflField (Just ro) = not (null (roTele ro))
    isReflField Nothing   = False

addC :: Env -> ConstInfo -> TC Env
addC e c = either throwTC pure (addConst e c)

foldMTC :: (b -> a -> TC b) -> b -> [a] -> TC b
foldMTC _ z []       = pure z
foldMTC f z (x : xs) = f z x >>= \z' -> foldMTC f z' xs

-- Telescopes ------------------------------------------------------------------

-- | Peel every leading @Pi@, reducing as needed, opening each binder as a local.
-- Reducing matters: a field type may be a definition that only unfolds to a
-- function type, and positivity has to look through that.
peelPis :: Expr -> TC ([Int], Expr)
peelPis = go []
  where
    go acc ty = whnf ty >>= \case
      Pi n dom cod -> do
        x <- freshFVar n dom
        go (x : acc) (inst1 (FVar x) cod)
      res -> pure (reverse acc, res)

-- | Open a recursive field's @xi@, handing the callback the locals and the
-- indices @pi@ instantiated at them.
withRecOcc :: RecOcc -> ([Int] -> [Expr] -> TC a) -> TC a
withRecOcc ro k = withLocals (roTele ro) $ \xs ->
  k xs (map (instN (reverse (map FVar xs))) (roIndices ro))

-- Constructor analysis --------------------------------------------------------

-- | The @ctor@ judgement.  Walks a constructor type left to right, classifying
-- each field as recursive or not, and checking
--
-- * strict positivity -- a member of the block occurs only as the head of a
--   field's final result, never in a domain and never inside the indices;
-- * the universe side condition @imax(l', l) <= l@ on every field, where @l'@
--   is the field's sort and @l@ the sort of the member being constructed;
-- * that the parameters are used unchanged, both by the result and by every
--   recursive occurrence.
--
-- A recursive field may land in /any/ member of the block; the result must land
-- in the member the constructor was declared for.
analyzeCtor :: [Name] -> [Level] -> [Int] -> Level -> Int -> Int -> Name -> Expr
            -> TC CtorShape
analyzeCtor names selfL ps indLvl nps owner cn cty0 = do
  _ <- inferSortOf cty0
  cty <- peelSharedParams ctxt nps ps cty0
  (flds, resIdx) <- goFields [] cty
  pure CtorShape { csName = cn, csOwner = owner, csFields = flds, csResIdx = resIdx }
  where
    iname = names !! owner
    ctxt  = "constructor " ++ showName cn ++ " of " ++ showName iname ++ ": "

    occursSelf e = any (`occursConst` e) names

    goFields acc ty = whnf ty >>= \case
      Pi n dom cod -> do
        l' <- inferSortOf dom
        -- imax(l', l) <= l.  When l = 0 this holds always (a Prop may quantify
        -- over anything); otherwise it amounts to l' <= l.
        unless (levelLeq (mkIMax l' indLvl) indLvl) $
          throwTC (ctxt ++ "field of sort " ++ showLevel l'
                   ++ " is too large for " ++ showName iname
                   ++ " : Sort " ++ showLevel indLvl)
        occ <- classifyField dom
        x <- freshFVar n dom
        goFields (CField x l' occ : acc) (inst1 (FVar x) cod)
      res -> do
        (j, idx) <- splitSelf "result type" res
        unless (j == owner) $
          throwTC (ctxt ++ "result type is headed by " ++ showName (names !! j)
                   ++ ", not by " ++ showName iname)
        pure (reverse acc, idx)

    -- A field either mentions no member of the block at all, or has the strictly
    -- positive shape @forall x::xi, t_k params idx@ with no member in @xi@ and
    -- none in @idx@.  Anything else -- a negative occurrence, or a member under
    -- another type constructor -- is rejected.  Nested inductives never reach
    -- here: "Front.Lower" has already turned them into extra members.
    --
    -- The occurs check is syntactic, so it also fires on an occurrence that is
    -- about to be erased: the specialised containers the nesting compilation
    -- builds routinely have fields like @(fun (x : T) => True) v@, where @T@
    -- appears only in a binder annotation of a redex.  Whenever the syntactic
    -- check fires the term is reduced and asked again, and only an occurrence
    -- that survives reduction counts.
    classifyField dom0
      | not (occursSelf dom0) = pure Nothing
      | otherwise = do
          dom <- whnf dom0
          if not (occursSelf dom) then pure Nothing else do
            (xs, res) <- peelPis dom
            forM_ xs $ \x -> do
              t <- localType x
              when (occursSelf t) $ do
                t' <- whnf t
                when (occursSelf t') $
                  throwTC (ctxt ++ "occurrence of the inductive block to the\
                                   \ left of an arrow")
            (j, idx) <- splitSelf "recursive field" res
            tele <- teleOf xs
            pure (Just (RecOcc j tele (map (abstractFVars xs) idx)))

    -- Require @res == t_j params idx@, and return @j@ and @idx@.
    splitSelf what res = do
      let (h, args) = unApps res
      case h of
        Const n ls | Just j <- elemIndex n names -> do
          unless (length ls == length selfL && and (zipWith levelEquiv ls selfL)) $
            throwTC (ctxt ++ what ++ " uses " ++ showName n
                     ++ " at the wrong universes")
          unless (length args >= nps) $
            throwTC (ctxt ++ what ++ ": " ++ showName n ++ " is not fully applied")
          let (pargs, iargs) = splitAt nps args
          unless (pargs == map FVar ps) $
            throwTC (ctxt ++ what ++ " must use the block's own parameters")
          forM_ iargs $ \a ->
            unless (not (occursSelf a)) $
              throwTC (ctxt ++ showName n ++ " may not occur in its own indices")
          pure (j, iargs)
        _ -> throwTC (ctxt ++ what ++ " must be headed by a type of the block, got "
                      ++ showExpr res)

-- Large elimination -------------------------------------------------------------

-- | Thesis §2.9.2.  A block eliminates into an arbitrary sort when either
--
-- 1. /every/ member is provably not a @Prop@ under any assignment of the
--    block's universes -- they share the motives, so the weakest decides; or
-- 2. the block has exactly one member and that member is a subsingleton: at
--    most one constructor, each of whose fields is either a proof or is
--    recovered from the result's indices.
--
-- The one-member side condition on case 2 is not decoration.  The subsingleton
-- licence is justified by reading the eliminator back as a function that
-- recovers the constructor's fields from the major premise's type, and that
-- argument is about /one/ inductive family: a mutual block's recursor also
-- carries motives and minor premises for its other members, whose data is not
-- recovered from anything.  The nesting compilation (SPEC.md §9) makes blocks
-- out of some declarations that were written as a single type, so a nested
-- @Prop@ loses the licence too -- correctly, since the container field it
-- nests under is data.
--
-- Case 2 is what makes @Eq.rec@, @And.rec@ and @Acc.rec@ large-eliminating while
-- @Exists.rec@ is not: @Exists.intro@'s witness is data that the result type
-- @Exists p@ does not mention, so it must not be allowed to escape.
--
-- \"Is a proof\" is read /absolutely/: the field's sort must be zero under every
-- assignment, not merely whenever the member itself lands in @Prop@.  The weaker,
-- relative reading @l' <= imax l' l@ is tempting and is what one reaches for to
-- justify a structure at @Sort (max u v)@ with fields at @u@ and @v@, but it is
-- not the rule.  @refs\/tests\/good\/tutorial\/093_MaybeProp.mk.ndjson@ pins this
-- down: @MaybeProp : Sort u@ has the single constructor
--
-- > MaybeProp.mk : PUnit.{u} -> (PUnit.{u} = PUnit.{u}) -> True -> MaybeProp.{u}
--
-- whose first field sits at @u@, and its exported recursor carries /one/ universe
-- parameter and a @Sort 0@ motive -- no large elimination.  The relative reading
-- would grant it, since @u <= imax u u@.
--
-- Nothing is lost by the strict reading.  The universe-polymorphic structures one
-- worries about are already covered by case 1: @PProd@ and @PSigma@ are declared
-- at @Sort (max 1 (max u v))@, which is provably non-zero, so they never reach
-- the subsingleton test at all.
decideLargeElim :: [(Level, [CtorShape])] -> Bool
decideLargeElim members
  | all (isDefinitelyNonZero . fst) members = True
  | [(_, shapes)] <- members = case shapes of
      []   -> True                      -- an empty Prop eliminates into anything
      [sh] -> all (recoverable sh) (csFields sh)
      _    -> False
  | otherwise = False
  where
    recoverable sh f =
      isDefinitelyZero (cfLevel f)
        || FVar (cfVar f) `elem` csResIdx sh

-- Recursors -----------------------------------------------------------------------

-- | Build one recursor per member,
--
-- > T_j.rec : forall params, forall C::kappa, forall e::eps,
-- >             forall a::alpha_j, forall (z : T_j params a), C_j a z
--
-- where the motives @C@ and the minor premises @e@ range over the /whole/ block,
-- in member order and then constructor order.  Each recursor carries iota rules
-- for its own member's constructors only; the shared prefix means a rule looks
-- the same whichever recursor of the block reduces it.
buildRecursors :: CoreBlock -> [IndInfo] -> [Int] -> [[(Binder, Expr)]]
               -> Bool -> Bool -> [[CtorShape]] -> TC [RecInfo]
buildRecursors cb inds ps idxTeles largeElim kLike shapess = do
  let lvls     = cbLevels cb
      selfL    = map LParam lvls
      elimName = freshLevelName (cbElimHint cb) lvls
      elimLvl  = if largeElim then LParam elimName else LZero
      recLvls  = if largeElim then elimName : lvls else lvls
      recNames = map cmRecName (cbMembers cb)
      nMembers = length inds
      selfApp ind as = mkApps (Const (indName ind) selfL) (map FVar ps ++ as)

  setLevelParams recLvls

  -- kappa_j = forall a::alpha_j, T_j params a -> Sort u
  motiveTys <- forM (zip inds idxTeles) $ \(ind, idxTele) ->
    withLocals idxTele $ \is ->
      closePis is (mkArrow (selfApp ind (map FVar is)) (Sort elimLvl))
  cVars <- forM (zip [1 :: Integer ..] motiveTys) $ \(k, t) ->
    freshFVar (Binder (if nMembers == 1 then str "motive"
                                        else mkNum (str "motive") k)) t

  -- eps_c = forall b::beta, forall v::delta, C_j p[b] (c params b)
  minorTys  <- mapM (minorType selfL ps cVars) (concat shapess)
  minorVars <- forM (zip [1 :: Integer ..] minorTys) $ \(k, t) ->
    freshFVar (Binder (mkNum (str "minor") k)) t

  forM (zip4 [0 ..] inds idxTeles shapess) $ \(j, ind, idxTele, shapes) -> do
    -- forall a::alpha_j, forall z : T_j params a, C_j a z
    concl <- withLocals idxTele $ \is -> do
      z <- freshFVar (Binder (str "t")) (selfApp ind (map FVar is))
      closePis (is ++ [z]) (mkApps (FVar (cVars !! j)) (map FVar is ++ [FVar z]))
    recTy <- closePis (ps ++ cVars ++ minorVars) concl
    _ <- inferSortOf recTy   -- audit: the derived type must itself typecheck

    let minorBase = length (concat (take j shapess))
    rules <- forM (zip [0 ..] shapes) $ \(k, sh) ->
      mkRule recNames recLvls ps cVars minorVars (minorBase + k) sh

    pure RecInfo
      { recName       = recNames !! j
      , recLevels     = recLvls
      , recType       = recTy
      , recInduct     = indName ind
      , recNumParams  = indNumParams ind
      , recNumMotives = nMembers
      , recNumIndices = indNumIndices ind
      , recNumMinors  = length minorVars
      , recRules      = rules
      , recK          = kLike
      }
  where
    zip4 (a : as) (b : bs) (c : cs) (d : ds) = (a, b, c, d) : zip4 as bs cs ds
    zip4 _ _ _ _                             = []

-- | @eps_c = forall b::beta, forall v::delta, C_j p[b] (c params b)@, where the
-- induction hypotheses @v@ come after /all/ the fields, one per recursive field,
-- each stated with the motive of the member that field lands in.
minorType :: [Level] -> [Int] -> [Int] -> CtorShape -> TC Expr
minorType selfL ps cVars sh = do
  ihs <- forM (zip [0 :: Integer ..] (csFields sh)) $ \(k, f) ->
    case cfRec f of
      Nothing -> pure Nothing
      Just ro -> do
        t <- withRecOcc ro $ \xs idx ->
          closePis xs (mkApps (FVar (cVars !! roMember ro))
                              (idx ++ [mkApps (FVar (cfVar f)) (map FVar xs)]))
        pure (Just (k, t))
  ihVars <- forM [ p | Just p <- ihs ] $ \(k, t) ->
    freshFVar (Binder (mkNum (str "ih") k)) t
  let ctorApp = mkApps (Const (csName sh) selfL)
                       (map FVar ps ++ map (FVar . cfVar) (csFields sh))
  closePis (map cfVar (csFields sh) ++ ihVars)
           (mkApps (FVar (cVars !! csOwner sh)) (csResIdx sh ++ [ctorApp]))

-- | The iota rule
--
-- > T_j.rec params C e p[b] (c params b)  ~>  e_c b v
-- > where v_i = fun x::xi_i => T_k.rec params C e pi_i[b,x] (b_i x)
--
-- Its right-hand side is stored abstracted over parameters, motives, minor
-- premises and fields, in that order -- which is the order
-- 'Kernel.Check.reduceRec' supplies them in.  Note that an induction hypothesis
-- calls the recursor of /its own/ member, which is what makes a mutual block
-- recurse across its types.
mkRule :: [Name] -> [Name] -> [Int] -> [Int] -> [Int] -> Int -> CtorShape
       -> TC RecRule
mkRule recNames recLvls ps cVars minorVars k sh = do
  let prefixArgs = map FVar ps ++ map FVar cVars ++ map FVar minorVars
  ihs <- forM (csFields sh) $ \f -> case cfRec f of
    Nothing -> pure Nothing
    Just ro -> fmap Just $ withRecOcc ro $ \xs idx ->
      closeLams xs (mkApps (Const (recNames !! roMember ro) (map LParam recLvls))
        (prefixArgs ++ idx ++ [mkApps (FVar (cfVar f)) (map FVar xs)]))
  let body = mkApps (FVar (minorVars !! k))
                    (map (FVar . cfVar) (csFields sh) ++ [ e | Just e <- ihs ])
  rhs <- closeLams (ps ++ cVars ++ minorVars ++ map cfVar (csFields sh)) body
  pure RecRule { rrCtor = csName sh, rrNumFields = csNumFields sh, rrRhs = rhs }

-- | A universe parameter name not already taken by the block.
freshLevelName :: Name -> [Name] -> Name
freshLevelName hint used
  | hint `notElem` used = hint
  | otherwise = head [ n | i <- [1 :: Integer ..]
                         , let n = mkNum hint i
                         , n `notElem` used ]
