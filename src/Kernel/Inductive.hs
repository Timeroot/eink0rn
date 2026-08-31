{-# LANGUAGE LambdaCase #-}
-- | Admitting a core inductive type, and deriving its recursor.
--
-- \"Core\" means /flat/ and /single/: one family over a parameter telescope,
-- with a plain telescope of indices ending in a sort.  Neither structure the
-- export format allows on top of that reaches this module.  Nesting -- a family
-- occurring underneath some other type constructor -- is compiled away by
-- "Front.Lower" (SPEC.md §9.1) into extra members of a mutual block, and the
-- mutual block is then compiled away (§9.3) into two single families: a tag type
-- and the block re-indexed by it.  So the core's inductive rule is the
-- one-family rule and nothing else.
--
-- The rules below follow Carneiro, /The Type Theory of Lean/ §2.9 -- the @ctor@
-- and @LE@ judgements, the shape of the recursor, and iota -- almost literally,
-- read at one family, which is the case §2.9 states before generalising to a
-- block.  SPEC.md §8 states them again in the notation used there.
--
-- Notation, as in the thesis:
--
-- > t : forall a::alpha, Sort l         the family, parameters in the context
-- > c : forall b::beta, t p[b]          a constructor
-- > b_i : forall x::xi_i, t pi_i[b,x]   a recursive field
--
-- Parameters are ordinary context variables here, exactly as in the thesis; the
-- outer @forall params@ is put back on at the very end.  Every occurrence of the
-- family inside its own constructors must be at those very parameters.
module Kernel.Inductive
  ( CoreInd (..)
  , AdmittedInd (..)
  , admitInd
  , freshLevelName
  ) where

import           Control.Monad (forM, forM_, unless, when)
import           Kernel.Check
import           Kernel.Env
import           Kernel.Expr
import           Kernel.Level
import           Kernel.Name

-- | One inductive family, in the shape the core accepts.
data CoreInd = CoreInd
  { coreLevels    :: ![Name]
  , coreNumParams :: !Int
  , coreName      :: !Name
  , coreArity     :: !Expr             -- ^ @forall params indices, Sort l@
  , coreCtors     :: ![(Name, Expr)]   -- ^ in constructor-index order
  , coreRecName   :: !Name
  , coreElimHint  :: !Name
    -- ^ preferred name for the fresh elimination universe; purely cosmetic, but
    -- reusing the exported one makes the derived recursor compare syntactically.
  }

data AdmittedInd = AdmittedInd
  { aiInd       :: !IndInfo
  , aiCtors     :: ![CtorInfo]
  , aiRec       :: !RecInfo
  , aiReflexive :: !Bool
    -- ^ some constructor has a recursive field /under a binder/, as
    -- @Acc.intro@'s @forall y, r y x -> Acc r y@ does.  No rule in this kernel
    -- consults it; it is derived so that "Front.Lower" can hold the export's
    -- @isReflexive@ to something.  ('indIsRecursive' plays the same part for
    -- @isRec@, and is on 'IndInfo' because reduction does use it.)
  }

-- | A recursive field @b_i : forall x::xi, t pi@.
data RecOcc = RecOcc
  { roTele    :: ![(Binder, Expr)]  -- ^ @xi@, a closed de Bruijn telescope
  , roIndices :: ![Expr]            -- ^ @pi@, de Bruijn relative to @xi@
  }

-- | One constructor field.
data CField = CField
  { cfVar   :: !Int             -- ^ the local standing for it
  , cfLevel :: !Level           -- ^ the sort its type lives in
  , cfRec   :: !(Maybe RecOcc)  -- ^ 'Nothing' when the field mentions the family
                                --   nowhere
  }

data CtorShape = CtorShape
  { csName   :: !Name
  , csFields :: ![CField]
  , csResIdx :: ![Expr]        -- ^ @p[b]@, mentioning the field locals
  }

csNumFields :: CtorShape -> Int
csNumFields = length . csFields

-- | Check an inductive type and derive its constructors and recursor.  The
-- environment must not already contain any of the names involved.
admitInd :: Env -> CoreInd -> Either String AdmittedInd
admitInd env ci = runTC env (coreLevels ci) (admit ci)

admit :: CoreInd -> TC AdmittedInd
admit ci = do
  env0 <- getEnv
  let lvls  = coreLevels ci
      selfL = map LParam lvls
      nps   = coreNumParams ci
      name  = coreName ci
      ctxt  = "inductive " ++ showName name ++ ": "

  unless (nps >= 0) $ throwTC (ctxt ++ "negative parameter count")

  -- 1. The arity must be a well-formed type, and must have at least as many
  --    leading binders as it declares parameters.
  _ <- inferSortOf (coreArity ci)
  let (paramTele, _) = unPisN nps (coreArity ci)
  unless (length paramTele == nps) $
    throwTC (ctxt ++ "declares " ++ show nps ++ " parameters but its type has "
             ++ show (length paramTele))

  -- 2. Constructors are checked with the family standing for itself as an opaque
  --    constant of exactly its declared arity, so a constructor cannot exploit
  --    anything about the contents of the type it is building.
  envSelf <- addC env0 (CAxiom name lvls (coreArity ci))
  (ps, indLvl, idxTele, shapes) <- withEnv envSelf $ withLocals paramTele $ \ps -> do
    rest <- peelSharedParams ctxt nps ps (coreArity ci)
    (is, res) <- peelPis rest
    lvl <- case res of
      Sort l -> pure l
      _      -> throwTC (ctxt ++ "the type must end in a sort, got " ++ showExpr res)
    tele <- teleOf is
    shs  <- forM (coreCtors ci) $ \(cn, cty) ->
      analyzeCtor name selfL ps lvl nps cn cty
    pure (ps, lvl, tele, shs)

  -- 3. Derived attributes.
  let largeElim = decideLargeElim indLvl shapes
      kLike     = case shapes of
        [sh] -> isDefinitelyZero indLvl && csNumFields sh == 0
        _    -> False
      indInfo = IndInfo
        { indName        = name
        , indLevels      = lvls
        , indType        = coreArity ci
        , indNumParams   = nps
        , indNumIndices  = length idxTele
        , indCtors       = map csName shapes
        , indIsRecursive = any (any (isRecField . cfRec) . csFields) shapes
        , indK           = kLike
        }
      ctorInfos =
        [ CtorInfo { ctorName      = cn
                   , ctorLevels    = lvls
                   , ctorType      = cty
                   , ctorInduct    = name
                   , ctorIdx       = k
                   , ctorNumParams = nps
                   , ctorNumFields = csNumFields sh
                   }
        | (k, (cn, cty), sh) <- zip3 [0 ..] (coreCtors ci) shapes ]

  envFull <- do
    e1 <- addC env0 (CInd indInfo)
    foldMTC (\e c -> addC e (CCtor c)) e1 ctorInfos

  recInfo <- withEnv envFull $
    buildRecursor ci indInfo ps idxTele largeElim kLike shapes

  pure (AdmittedInd indInfo ctorInfos recInfo
          (any (any (isReflField . cfRec) . csFields) shapes))
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
-- * strict positivity -- the family occurs only as the head of a field's final
--   result, never in a domain and never inside the indices;
-- * the universe side condition @imax(l', l) <= l@ on every field, where @l'@
--   is the field's sort and @l@ the sort the family lands in;
-- * that the parameters are used unchanged, both by the result and by every
--   recursive occurrence.
analyzeCtor :: Name -> [Level] -> [Int] -> Level -> Int -> Name -> Expr
            -> TC CtorShape
analyzeCtor iname selfL ps indLvl nps cn cty0 = do
  _ <- inferSortOf cty0
  cty <- peelSharedParams ctxt nps ps cty0
  (flds, resIdx) <- goFields [] cty
  pure CtorShape { csName = cn, csFields = flds, csResIdx = resIdx }
  where
    ctxt = "constructor " ++ showName cn ++ " of " ++ showName iname ++ ": "

    occursSelf = occursConst iname

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
        idx <- splitSelf "result type" res
        pure (reverse acc, idx)

    -- A field either does not mention the family at all, or has the strictly
    -- positive shape @forall x::xi, t params idx@ with the family in neither
    -- @xi@ nor @idx@.  Anything else -- a negative occurrence, or the family
    -- under another type constructor -- is rejected.  Nested inductives never
    -- reach here: "Front.Lower" has already turned them into separate types.
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
                  throwTC (ctxt ++ "occurrence of the inductive type to the\
                                   \ left of an arrow")
            idx  <- splitSelf "recursive field" res
            tele <- teleOf xs
            pure (Just (RecOcc tele (map (abstractFVars xs) idx)))

    -- Require @res == t params idx@, and return @idx@.
    splitSelf what res = do
      let (h, args) = unApps res
      case h of
        Const n ls | n == iname -> do
          unless (length ls == length selfL && and (zipWith levelEquiv ls selfL)) $
            throwTC (ctxt ++ what ++ " uses " ++ showName n
                     ++ " at the wrong universes")
          unless (length args >= nps) $
            throwTC (ctxt ++ what ++ ": " ++ showName n ++ " is not fully applied")
          let (pargs, iargs) = splitAt nps args
          unless (pargs == map FVar ps) $
            throwTC (ctxt ++ what ++ " must use the type's own parameters")
          forM_ iargs $ \a ->
            unless (not (occursSelf a)) $
              throwTC (ctxt ++ showName n ++ " may not occur in its own indices")
          pure iargs
        _ -> throwTC (ctxt ++ what ++ " must be headed by " ++ showName iname
                      ++ ", got " ++ showExpr res)

-- Large elimination -------------------------------------------------------------

-- | Thesis §2.9.2.  A type eliminates into an arbitrary sort when either
--
-- 1. it is provably not a @Prop@ under any assignment of its universes; or
-- 2. it is a subsingleton: at most one constructor, each of whose fields is
--    either a proof or is recovered from the result's indices.
--
-- Case 2 is what makes @Eq.rec@, @And.rec@ and @Acc.rec@ large-eliminating while
-- @Exists.rec@ is not: @Exists.intro@'s witness is data that the result type
-- @Exists p@ does not mention, so it must not be allowed to escape.
--
-- The rule is stated for /one/ family, and that is not an accident of this
-- module now taking only one.  The subsingleton licence is justified by reading
-- the eliminator back as a function that recovers the constructor's fields from
-- the major premise's type, and that argument is about a single family: a mutual
-- block's recursor also carries motives and minor premises for its other
-- members, whose data is recovered from nothing.  So the flattening of SPEC.md
-- §9.3 does /not/ hand the block the licence its flat type gets here; it builds
-- the block's recursors at case 1 only.  The same goes for the nesting
-- compilation, which makes several types out of a declaration written as one, so
-- a nested @Prop@ loses the licence too -- correctly, since the container field
-- it nests under is data.
--
-- \"Is a proof\" is read /absolutely/: the field's sort must be zero under every
-- assignment, not merely whenever the type itself lands in @Prop@.  The weaker,
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
decideLargeElim :: Level -> [CtorShape] -> Bool
decideLargeElim lvl shapes
  | isDefinitelyNonZero lvl = True
  | otherwise = case shapes of
      []   -> True                      -- an empty Prop eliminates into anything
      [sh] -> all (recoverable sh) (csFields sh)
      _    -> False
  where
    recoverable sh f =
      isDefinitelyZero (cfLevel f)
        || FVar (cfVar f) `elem` csResIdx sh

-- Recursors -----------------------------------------------------------------------

-- | Build the recursor,
--
-- > t.rec : forall params, forall C::kappa, forall e::eps,
-- >           forall a::alpha, forall (z : t params a), C a z
--
-- with one minor premise per constructor, in constructor order.
buildRecursor :: CoreInd -> IndInfo -> [Int] -> [(Binder, Expr)] -> Bool -> Bool
              -> [CtorShape] -> TC RecInfo
buildRecursor ci ind ps idxTele largeElim kLike shapes = do
  let lvls     = coreLevels ci
      selfL    = map LParam lvls
      elimName = freshLevelName (coreElimHint ci) lvls
      elimLvl  = if largeElim then LParam elimName else LZero
      recLvls  = if largeElim then elimName : lvls else lvls
      selfApp as = mkApps (Const (indName ind) selfL) (map FVar ps ++ as)

  setLevelParams recLvls

  -- kappa = forall a::alpha, t params a -> Sort u
  motiveTy <- withLocals idxTele $ \is ->
    closePis is (mkArrow (selfApp (map FVar is)) (Sort elimLvl))
  cVar <- freshFVar (Binder (str "motive")) motiveTy

  -- eps_c = forall b::beta, forall v::delta, C p[b] (c params b)
  minorTys  <- mapM (minorType selfL ps cVar) shapes
  minorVars <- forM (zip [1 :: Integer ..] minorTys) $ \(k, t) ->
    freshFVar (Binder (mkNum (str "minor") k)) t

  -- forall a::alpha, forall z : t params a, C a z
  concl <- withLocals idxTele $ \is -> do
    z <- freshFVar (Binder (str "t")) (selfApp (map FVar is))
    closePis (is ++ [z]) (mkApps (FVar cVar) (map FVar is ++ [FVar z]))
  recTy <- closePis (ps ++ [cVar] ++ minorVars) concl
  _ <- inferSortOf recTy   -- audit: the derived type must itself typecheck

  rules <- forM (zip [0 ..] shapes) $ \(k, sh) ->
    mkRule (coreRecName ci) recLvls ps cVar minorVars k sh

  pure RecInfo
    { recName       = coreRecName ci
    , recLevels     = recLvls
    , recType       = recTy
    , recInduct     = indName ind
    , recNumParams  = indNumParams ind
    , recNumMotives = 1
    , recNumIndices = indNumIndices ind
    , recNumMinors  = length minorVars
    , recRules      = rules
    , recK          = kLike
    }

-- | @eps_c = forall b::beta, forall v::delta, C p[b] (c params b)@, where the
-- induction hypotheses @v@ come after /all/ the fields, one per recursive field.
minorType :: [Level] -> [Int] -> Int -> CtorShape -> TC Expr
minorType selfL ps cVar sh = do
  ihs <- forM (zip [0 :: Integer ..] (csFields sh)) $ \(k, f) ->
    case cfRec f of
      Nothing -> pure Nothing
      Just ro -> do
        t <- withRecOcc ro $ \xs idx ->
          closePis xs (mkApps (FVar cVar)
                              (idx ++ [mkApps (FVar (cfVar f)) (map FVar xs)]))
        pure (Just (k, t))
  ihVars <- forM [ p | Just p <- ihs ] $ \(k, t) ->
    freshFVar (Binder (mkNum (str "ih") k)) t
  let ctorApp = mkApps (Const (csName sh) selfL)
                       (map FVar ps ++ map (FVar . cfVar) (csFields sh))
  closePis (map cfVar (csFields sh) ++ ihVars)
           (mkApps (FVar cVar) (csResIdx sh ++ [ctorApp]))

-- | The iota rule
--
-- > t.rec params C e p[b] (c params b)  ~>  e_c b v
-- > where v_i = fun x::xi_i => t.rec params C e pi_i[b,x] (b_i x)
--
-- Its right-hand side is stored abstracted over parameters, motive, minor
-- premises and fields, in that order -- which is the order
-- 'Kernel.Check.reduceRec' supplies them in.
mkRule :: Name -> [Name] -> [Int] -> Int -> [Int] -> Int -> CtorShape
       -> TC RecRule
mkRule recNm recLvls ps cVar minorVars k sh = do
  let prefixArgs = map FVar ps ++ [FVar cVar] ++ map FVar minorVars
  ihs <- forM (csFields sh) $ \f -> case cfRec f of
    Nothing -> pure Nothing
    Just ro -> fmap Just $ withRecOcc ro $ \xs idx ->
      closeLams xs (mkApps (Const recNm (map LParam recLvls))
        (prefixArgs ++ idx ++ [mkApps (FVar (cfVar f)) (map FVar xs)]))
  let body = mkApps (FVar (minorVars !! k))
                    (map (FVar . cfVar) (csFields sh) ++ [ e | Just e <- ihs ])
  rhs <- closeLams (ps ++ [cVar] ++ minorVars ++ map cfVar (csFields sh)) body
  pure RecRule { rrCtor = csName sh, rrNumFields = csNumFields sh, rrRhs = rhs }

-- | A universe parameter name not already taken by the type.
freshLevelName :: Name -> [Name] -> Name
freshLevelName hint used
  | hint `notElem` used = hint
  | otherwise = head [ n | i <- [1 :: Integer ..]
                         , let n = mkNum hint i
                         , n `notElem` used ]
