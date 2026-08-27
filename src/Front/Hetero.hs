{-# LANGUAGE LambdaCase #-}

-- | Lowering a mutual block whose members do not all land in the same universe.
--
-- Every Lean kernel this one has been compared against rejects such a block out
-- of hand, and @lean4export@ will never emit one, so nothing in the arena
-- exercises this module.  It is here because the rejection is not a consequence
-- of the type theory: SPEC.md §8.4's per-field condition @imax(l', l) <= l@ is
-- vacuous when @l@ is zero, so a @Prop@ member cuts the chain of inequalities
-- that would otherwise force a cycle of data members to share a level -- and the
-- @Prop@ that cuts it is the same @Prop@ whose proof irrelevance collapses the
-- injection a Russell paradox would need.  The block is sound; it is merely
-- unstudied.
--
-- So it is admitted the way §9.3 admits a homogeneous block: not believed, but
-- /derived/ from types this kernel already knows how to admit, with every
-- constant the file declares checked against the derivation and every iota rule
-- checked to hold definitionally.  Three ingredients:
--
-- [The shadow] The whole block again, verbatim, with every member's result sort
--   replaced by @Prop@.  That block /is/ homogeneous, so §9.3 takes it.  It is
--   what the @Prop@ members are defined to be, and -- because the flattening
--   sees every member occurrence at once -- it is also the block's positivity
--   witness.
--
-- [The components] Each data member, declared on its own at the universe it
--   asks for.  Its fields that point at a @Prop@ member point at the shadow,
--   which is already in the environment and is not part of the declaration, so
--   the cycle is gone; what is left is the data-only dependency graph, whose
--   strongly connected components are provably level-homogeneous and are
--   therefore admitted, in topological order, by §9.3 again.
--
-- [The pairing] @Sig a b : Prop@, a @Prop@-valued dependent pair with small
--   elimination only.  A @Prop@ member's recursor has to produce motives for
--   the data members too, and it only has the shadow to recurse over; @Sig@ is
--   how the shadow's recursion carries a data member's motive along without
--   ever eliminating a proof into data.
--
-- What this deliberately does /not/ do is touch SPEC.md §8.5.  Heterogeneity is
-- about which blocks are well-formed; subsingleton elimination is about what a
-- recursor may then eliminate into, and the one-member side condition on it
-- stays exactly where it is.
module Front.Hetero
  ( resultLevels
  , heteroBlock
  ) where

import           Control.Monad         (foldM, forM, forM_, unless, when)
import qualified Data.ByteString.Char8 as B
import           Data.Graph            (flattenSCC, stronglyConnComp)
import           Data.List             (elemIndex, find, nub)
import           Front.Block
import           Front.Export
import           Kernel.Check
import           Kernel.Env
import           Kernel.Expr
import           Kernel.Inductive
import           Kernel.Level
import           Kernel.Name

-- | The sort each member of a block ends in.
--
-- An arity may not mention the block -- the core checks arities in the
-- environment the block is declared /into/ -- so this is readable before
-- anything about the block has been admitted, which is what lets the caller
-- decide which of the two lowerings to run.
resultLevels :: Env -> String -> [Name] -> Int -> [(Binder, Expr)] -> [CoreMember]
             -> Either String [Level]
resultLevels env ctxt lvls nps paramTele members =
  runTC env lvls $ withLocals paramTele $ \ps ->
    forM members $ \m -> snd <$> openArity ctxt nps ps (cmArity m)

-- | What one constructor field is, as far as this pass cares.
--
-- @Nothing@: the block does not occur in it.  @Just (j, under)@: it ends in
-- member @j@, and @under@ says whether it does so under binders -- a field of
-- type @Nat -> D@ rather than of type @D@.
type FieldOcc = Maybe (Int, Bool)

-- | Admit a block whose members land in different universes.
--
-- @resLvls@ is 'resultLevels', which the caller has already found not to be
-- constant.  There is no nesting: §9.1's auxiliaries would each need a member
-- of their own here, and the caller rejects that combination before we are
-- reached.
heteroBlock :: Env -> [[ExCtor]] -> [CoreMember] -> [Level] -> [(Binder, Expr)]
            -> [Name] -> Int -> [ExRec] -> Name -> Either String BlockResult
heteroBlock env0 groups members resLvls paramTele lvls nps recs privRoot = do
  let n           = length members
      memNames    = map cmName members
      selfL       = map LParam lvls
      ctxt        = "the heterogeneous block of " ++ showName (head memNames) ++ ": "
      cctxt cn    = ctxt ++ "constructor " ++ showName cn ++ ": "
      isProp i    = levelEquiv (resLvls !! i) LZero
      propIs      = filter isProp [0 .. n - 1]
      dataIs      = filter (not . isProp) [0 .. n - 1]
      nCtors      = map (length . cmCtors) members
      ctorsOf i   = cmCtors (members !! i)
      absCtor i k = sum (take i nCtors) + k
      recNameOf i = cmRecName (members !! i)

      -- Every name this pass invents hangs off the block's private root, which
      -- is a 'Priv' and so cannot be written by any file (SPEC.md §9.3).  Unlike
      -- the flattening, most of these survive into the environment the caller
      -- gets: a @Prop@ member's constructor is defined in terms of a squash map,
      -- which is defined in terms of a component's recursor, and the definitions
      -- are the constants the file declared.
      pv s        = mkStr privRoot (B.pack s)
      shRoot      = pv "sh"
      shTy i      = mkNum shRoot (toInteger i)
      shCtorN i k = mkNum (shTy i) (toInteger k)
      shRecN i    = mkStr (shTy i) (B.pack "rec")
      dRoot c     = mkNum (pv "d") (toInteger c)
      drName j    = mkNum (pv "dr") (toInteger j)
      sqName j    = mkNum (pv "sq") (toInteger j)
      sigTy       = pv "sig"
      sigMk       = mkStr sigTy (B.pack "mk")
      sigRec      = mkStr sigTy (B.pack "rec")

      toShadow    = renameConsts (zip memNames (map shTy [0 .. n - 1]))
      unShadow nm = maybe nm id (lookup nm (zip (map shTy [0 .. n - 1]) memNames))

      -- One elimination universe for the whole block, and a motive per member at
      -- the sort that member's own recursor may eliminate into.  Every recursor
      -- of a block takes every member's motive, so there is no other shape
      -- available: a @Prop@ member's recursor quantifies over a @Sort u@-valued
      -- motive it will only ever pass on to a data member's.
      elimName    = freshLevelName (elimHint (map exrLevels recs) lvls) lvls
      anyLarge    = any (isDefinitelyNonZero . (resLvls !!)) [0 .. n - 1]
      recLps      = if anyLarge then elimName : lvls else lvls
      recUs       = map LParam recLps
      elimLvl i | isDefinitelyNonZero (resLvls !! i) = LParam elimName
                | otherwise                          = LZero

      runE what env ls act =
        either (\e -> Left (ctxt ++ what ++ e)) Right (runTC env ls act)
      runE_ what env ls act = () <$ runE what env ls act

  unless (n >= 2) $
    Left (ctxt ++ "internal: a block of one type cannot be heterogeneous")
  unless (length groups == n && map length groups == nCtors) $
    Left (ctxt ++ "internal: the exported constructors do not match the members")

  ------------------------------------------------------------------ 1. shadow.
  -- The block again with every result sort replaced by @Prop@ and every member
  -- occurrence redirected to the copy.  Nothing else moves: an arity's index
  -- telescope and a constructor's fields are reused verbatim, so a shape the
  -- shadow accepts is a shape the block has.
  (nIdxs, shMembers) <- runE "" env0 lvls $ withLocals paramTele $ \ps -> do
    ms <- forM (zip [0 :: Int ..] members) $ \(i, m) -> do
      _ <- inferSortOf (cmArity m)
      (is, _) <- openArity ctxt nps ps (cmArity m)
      ar <- closePis (ps ++ is) (Sort LZero)
      pure ( length is
           , CoreMember { cmName    = shTy i
                        , cmArity   = ar
                        , cmCtors   = [ (shCtorN i k, toShadow cty)
                                      | (k, (_, cty)) <- zip [0 :: Int ..] (cmCtors m) ]
                        , cmRecName = shRecN i } )
    pure (map fst ms, map snd ms)

  -- Running the shadow through §9.3 first is deliberate: positivity, the
  -- universe conditions on fields, and the discipline that every occurrence be
  -- at the block's own parameters and all of its indices are all decided there,
  -- by the code the whole corpus exercises, and reported against the member the
  -- file actually declared.
  shb <- flattenCore env0 (ctxt ++ "in its all-Prop shadow, ") unShadow
                     shMembers paramTele lvls nps (str "u") shRoot
  envSh <- foldM addConst env0
    (  map CInd (cbInds shb) ++ map CCtor (concat (cbCtors shb))
    ++ map CRec (cbRecs shb) )
  forM_ (cbRecs shb) $ \r -> do
    unless (length (recLevels r) == length lvls) $
      Left (ctxt ++ "internal: the all-Prop shadow eliminates into every sort")
    unless (recNumMotives r == n && recNumMinors r == sum nCtors) $
      Left (ctxt ++ "internal: the shadow's recursor has the wrong arity")
    runE_ ("internal: the shadow's recursor " ++ showName (recName r)
           ++ " does not typecheck: ") envSh (recLevels r) (inferSortOf (recType r))
    checkRecRules envSh r

  --------------------------------------------------------------- 2. the pair.
  -- @Sig a b@ is a @Prop@ whose proofs carry an @a@ and a proof of @b@ of it.
  -- Small elimination is the whole point -- 'decideLargeElim' must deny it, or
  -- the @a@ could be projected back out of a proof and the block really would
  -- be unsound -- so the only thing it can be eliminated into is another
  -- @Prop@, which is exactly what a shadow motive is.
  let lu       = LParam (str "u")
      lv       = LParam (str "v")
      bnd      = Binder . str
      sigArity = Pi (bnd "a") (Sort lu)
                   (Pi (bnd "b") (Pi (bnd "x") (BVar 0) (Sort lv)) (Sort LZero))
      sigMkTy  = Pi (bnd "a") (Sort lu)
                   (Pi (bnd "b") (Pi (bnd "x") (BVar 0) (Sort lv))
                     (Pi (bnd "fst") (BVar 1)
                       (Pi (bnd "snd") (App (BVar 1) (BVar 0))
                         (mkApps (Const sigTy [lu, lv]) [BVar 3, BVar 2]))))
  aiSig <- either (\e -> Left (ctxt ++ "internal: the pairing type: " ++ e)) Right $
    admitInd envSh CoreInd
      { coreLevels    = [str "u", str "v"]
      , coreNumParams = 2
      , coreName      = sigTy
      , coreArity     = sigArity
      , coreCtors     = [(sigMk, sigMkTy)]
      , coreRecName   = sigRec
      , coreElimHint  = str "w"
      }
  unless (length (recLevels (aiRec aiSig)) == 2) $
    Left (ctxt ++ "internal: the pairing type eliminates into every sort")
  envSig <- foldM addConst envSh
    (CInd (aiInd aiSig) : map CCtor (aiCtors aiSig) ++ [CRec (aiRec aiSig)])

  --------------------------------------------------- 3. the @Prop@ members.
  -- A @Prop@ member simply /is/ its shadow: same arity, same constructors, same
  -- sort.  It is a definition and not an inductive type, which is a real
  -- divergence and is recorded in SPEC.md: @proj@ on it is rejected, and a
  -- later block may not nest inside it.
  forM_ propIs $ \i ->
    runE_ (showName (memNames !! i) ++ " does not have the type it declares once \
           \the block's propositions are read off its all-Prop shadow: ")
          envSig lvls (checkType (Const (shTy i) selfL) (cmArity (members !! i)))
  envTy <- foldM addConst envSig
    [ CDef DefInfo { defName   = memNames !! i
                   , defLevels = lvls
                   , defType   = cmArity (members !! i)
                   , defValue  = Const (shTy i) selfL
                   , defHint   = HAbbrev }
    | i <- propIs ]

  ------------------------------------------------------------ 4. the scan.
  -- Which member, if any, each constructor field recurses into.  Done once, in
  -- an environment where every member is an /axiom/, so that no member can be
  -- unfolded into its shadow and hide an occurrence; the answers are then reused
  -- in all three views of the block, which is sound because the shadow's
  -- flattening has already refused any field whose binders or index arguments
  -- mention a member (so those parts of a field are the same term in every
  -- view, and only the head constant moves).
  envScan <- foldM addConst env0
    [ CAxiom (cmName m) lvls (cmArity m) | m <- members ]
  occs <- runE "" envScan lvls $ withLocals paramTele $ \ps ->
    forM (zip [0 ..] members) $ \(i, m) ->
      forM (cmCtors m) $ \(cn, cty) ->
        scanCtor (cctxt cn) memNames selfL nIdxs nps ps i cty

  let ihIdx p fs r = length (filter p (take r fs))
      recFields fs = [ (r, j, u) | (r, Just (j, u)) <- zip [0 :: Int ..] fs ]

  -- The one shape this construction cannot reach.  A field @xi -> D@ into a data
  -- member, inside a block that has a @Prop@ member, would need the @Prop@
  -- member's recursor to turn @xi -> Sig D (C D)@ into @xi -> D@, and pulling a
  -- data value out from under a binder inside a proof is exactly what choice is
  -- for.  Rejecting is the conservative answer, and it costs nothing that a
  -- homogeneous block could have expressed.
  unless (null propIs) $
    forM_ (zip [0 ..] occs) $ \(i, cs) ->
      forM_ (zip (map fst (ctorsOf i)) cs) $ \(cn, fs) ->
        forM_ (recFields fs) $ \(_, j, under) ->
          when (under && not (isProp j)) $
            Left (cctxt cn ++ "a field of the form \"... -> " ++ showName (memNames !! j)
                  ++ "\" recurses into a member of the block that is not a \
                     \proposition, in a block that has one; lowering that shape \
                     \definitionally would need choice")

  ---------------------------------------------------- 5. the data components.
  -- With the @Prop@ members standing on their own, the block's dependency graph
  -- restricted to the data members is all that is left of the cycle, and each of
  -- its strongly connected components is level-homogeneous -- which is what
  -- makes it something §9.3 can already admit.  'stronglyConnComp' hands them
  -- back dependencies first, which is the order they have to be declared in.
  let deps i = nub [ j | fs <- occs !! i, Just (j, _) <- fs ]
      sccs   = map flattenSCC (stronglyConnComp
                 [ (i, i, filter (`elem` dataIs) (deps i)) | i <- dataIs ])
      sccOf j = case [ sc | sc <- sccs, j `elem` sc ] of
                  (sc : _) -> sc
                  []       -> [j]
  forM_ sccs $ \sc -> forM_ sc $ \j ->
    unless (levelEquiv (resLvls !! head sc) (resLvls !! j)) $
      Left (ctxt ++ showName (memNames !! j) ++ " and "
            ++ showName (memNames !! head sc) ++ " depend on each other but do \
               \not land in the same universe, so no ordering of the block's \
               \data members can break the cycle")

  -- A component is derived at the block's own constructor types, not at
  -- rewritten ones: a field pointing at a @Prop@ member points at a definition
  -- that is already in the environment and is not part of this declaration, so
  -- 'analyzeCtor' sees an ordinary non-recursive field of an ordinary type.
  -- That is the whole trick, and it is why the constants a component leaves
  -- behind are the block's own.
  (envD, dRecs) <- foldM
    (\(env, acc) (c, sc) -> do
      let cctx = ctxt ++ "in the data component of "
                 ++ showName (memNames !! head sc) ++ ", "
          dms = [ CoreMember { cmName    = memNames !! j
                             , cmArity   = cmArity (members !! j)
                             , cmCtors   = ctorsOf j
                             , cmRecName = drName j }
                | j <- sc ]
      cb <- flattenCore env cctx id dms paramTele lvls nps (str "u") (dRoot c)
      -- 'indIsRecursive' as the component sees it under-reports: a member whose
      -- only recursion goes out through a proposition and back looks flat from
      -- here.  The flag is read by 'Kernel.Env.isStructureLike' and nowhere
      -- else, where over-reporting costs eta and under-reporting is a rule
      -- firing where the block says it should not, so it is recomputed against
      -- the whole block.
      let blockRec j = or [ occursConst nm cty
                          | (_, cty) <- ctorsOf j, nm <- memNames ]
          inds' = [ i { indIsRecursive = blockRec j } | (j, i) <- zip sc (cbInds cb) ]
      forM_ (cbInds cb) $ \i -> when (indK i) $
        Left (cctx ++ "internal: a data component claims K-like reduction")
      env' <- foldM addConst env
        (  map CInd inds' ++ map CCtor (concat (cbCtors cb))
        ++ map CRec (cbRecs cb) )
      forM_ (cbRecs cb) $ \r -> do
        runE_ ("internal: " ++ showName (recName r) ++ " does not typecheck: ")
              env' (recLevels r) (inferSortOf (recType r))
        checkRecRules env' r
      pure (env', acc ++ zip sc (cbRecs cb)))
    (envTy, []) (zip [0 :: Int ..] sccs)
  let drOf j = case lookup j dRecs of
                 Just r  -> Right r
                 Nothing -> Left (ctxt ++ "internal: no component recursor for "
                                  ++ showName (memNames !! j))

  ----------------------------------------------------- 6. the squash maps.
  -- @sq_j@ sends a data member to its shadow, by structural recursion on the
  -- component: each constructor is rebuilt as the shadow's, with the fields that
  -- point back into the block squashed on the way.  It is what a @Prop@ member's
  -- constructor uses to store a data argument, and the only reason a component's
  -- recursor has to survive into the final environment at all.
  sqDefs <- forM dataIs $ \j -> do
    dr <- drOf j
    let sc  = sccOf j
        big = length (recLevels dr) > length lvls
        us  = [ LZero | big ] ++ selfL
    v <- runE ("internal: the squash map of " ++ showName (memNames !! j) ++ ": ")
              envD lvls $ withLocals paramTele $ \ps -> do
      motives <- forM sc $ \s -> do
        (is, _) <- openArity ctxt nps ps (cmArity (members !! s))
        w <- freshFVar (bnd "t") (mkApps (Const (memNames !! s) selfL)
                                         (map FVar ps ++ map FVar is))
        closeLams (is ++ [w]) (mkApps (Const (shTy s) selfL)
                                      (map FVar ps ++ map FVar is))
      mts <- minorTelescope ctxt nps ps dr us motives
      gs <- forM (zip mts [ (s, k) | s <- sc, k <- [0 .. nCtors !! s - 1] ]) $
        \((_, mt), (s, k)) -> do
          let fs   = occs !! s !! k
              nf   = length fs
              same = \o -> case o of Just (j', _) -> j' `elem` sc; Nothing -> False
              nih  = length (filter same fs)
          tele <- teleOfPis ctxt (nf + nih) mt
          withLocals tele $ \xs -> do
            let (fvs, ihvs) = splitAt nf xs
            args <- forM (zip [0 ..] fs) $ \(r, o) -> case o of
              Just (j', _) | j' `elem` sc -> pure (FVar (ihvs !! ihIdx same fs r))
                           | not (isProp j') ->
                             peelOcc nps (fvs !! r) $ \ys pir ->
                               closeLams ys (mkApps (Const (sqName j') selfL)
                                 (map FVar ps ++ pir
                                  ++ [mkApps (FVar (fvs !! r)) (map FVar ys)]))
              _ -> pure (FVar (fvs !! r))
            closeLams xs (mkApps (Const (shCtorN s k) selfL) (map FVar ps ++ args))
      closeLams ps (mkApps (Const (drName j) us)
                           (map FVar ps ++ motives ++ gs))
    ty <- runE "internal: the type of a squash map: " envD lvls $
      withLocals paramTele $ \ps -> do
        (is, _) <- openArity ctxt nps ps (cmArity (members !! j))
        z <- freshFVar (bnd "t") (mkApps (Const (memNames !! j) selfL)
                                         (map FVar ps ++ map FVar is))
        closePis (ps ++ is ++ [z]) (mkApps (Const (shTy j) selfL)
                                           (map FVar ps ++ map FVar is))
    pure DefInfo { defName = sqName j, defLevels = lvls, defType = ty
                 , defValue = v, defHint = HAbbrev }
  -- Each squash map only mentions the component recursors of members it
  -- reaches, which are all in place, so they go in one at a time in the order
  -- the components were derived.
  envSq <- foldM (\env d -> do
                    runE_ ("internal: the squash map of " ++ showName (defName d)
                           ++ " does not typecheck: ")
                          env lvls (checkType (defValue d) (defType d))
                    addConst env (CDef d))
                 envD [ d | j <- concat sccs, d <- sqDefs, defName d == sqName j ]

  ------------------------------------------------ 7. the block's constructors.
  -- A data member's constructors are already in the environment, at the block's
  -- own types, because that is how its component was declared.  A @Prop@
  -- member's are definitions: the shadow's constructor, with each field that
  -- points at a data member squashed.  Unlike the recursor below, this one has
  -- no gap -- @sq_j@ is a function, so it goes under a binder without trouble.
  ctorDefs <- forM propIs $ \i ->
    forM (zip3 [0 :: Int ..] (ctorsOf i) (occs !! i)) $ \(k, (cn, cty), fs) -> do
      v <- runE (cctxt cn) envSq lvls $ withLocals paramTele $ \ps ->
        openCtor (cctxt cn) nps ps cty (length fs) $ \bs _ -> do
          args <- forM (zip [0 ..] fs) $ \(r, o) -> case o of
            Just (j, _) | not (isProp j) ->
              peelOcc nps (bs !! r) $ \ys pir ->
                closeLams ys (mkApps (Const (sqName j) selfL)
                  (map FVar ps ++ pir ++ [mkApps (FVar (bs !! r)) (map FVar ys)]))
            _ -> pure (FVar (bs !! r))
          closeLams (ps ++ bs) (mkApps (Const (shCtorN i k) selfL)
                                       (map FVar ps ++ args))
      pure DefInfo { defName = cn, defLevels = lvls, defType = cty
                   , defValue = v, defHint = HAbbrev }
  forM_ (concat ctorDefs) $ \d ->
    runE_ ("constructor " ++ showName (defName d) ++ " is not the one the \
           \block's all-Prop shadow gives it: ")
          envSq lvls (checkType (defValue d) (defType d))
  envC <- foldM addConst envSq (map CDef (concat ctorDefs))

  -- Whatever the file says a constructor's type is, it has to be the one the
  -- block gives it.  For a data member the two were already compared when its
  -- component was admitted; doing it for every member costs one defeq check and
  -- keeps the guarantee uniform.
  forM_ (zip (concat groups) (concatMap (map snd . ctorsOf) [0 .. n - 1])) $
    \(c, cty) -> runE_ (cctxt (excName c)) envC lvls $ do
      ok <- isDefEq (excType c) cty
      unless ok $ throwTC ("the exported type is not the one the block gives it\
                           \\n  exported " ++ showExpr (excType c)
                           ++ "\n  derived  " ++ showExpr cty)

  ------------------------------------------------------- 8. the recursors.
  -- Their types and their reduction rules are the block's own -- written out
  -- exactly as SPEC.md §8.6 and §8.7 would have written them for a mutual block
  -- the core could take -- and are built once here.  What each recursor's
  -- /value/ is depends on which member it eliminates, and is built below.
  let withRecCtx :: ([Int] -> [Int] -> [Int] -> TC a) -> TC a
      withRecCtx k = withLocals paramTele $ \ps -> do
        kappas <- forM [0 .. n - 1] $ \i -> do
          (is, _) <- openArity ctxt nps ps (cmArity (members !! i))
          closePis is (mkArrow (mkApps (Const (memNames !! i) selfL)
                                       (map FVar ps ++ map FVar is))
                               (Sort (elimLvl i)))
        cVars <- forM (zip [1 :: Integer ..] kappas) $ \(i, t) ->
          freshFVar (Binder (mkNum (str "motive") i)) t
        minors <- forM [0 .. n - 1] $ \i ->
          forM (zip (ctorsOf i) (occs !! i)) $ \((cn, cty), fs) ->
            openCtor ctxt nps ps cty (length fs) $ \bs ridx -> do
              ihts <- forM (recFields fs) $ \(r, j, _) ->
                peelOcc nps (bs !! r) $ \ys pir ->
                  closePis ys (mkApps (FVar (cVars !! j))
                    (pir ++ [mkApps (FVar (bs !! r)) (map FVar ys)]))
              ihvs <- forM (zip [1 :: Integer ..] ihts) $ \(q, t) ->
                freshFVar (Binder (mkNum (str "ih") q)) t
              closePis (bs ++ ihvs) (mkApps (FVar (cVars !! i))
                (ridx ++ [mkApps (Const cn selfL) (map FVar ps ++ map FVar bs)]))
        eVars <- forM (zip [1 :: Integer ..] (concat minors)) $ \(q, t) ->
          freshFVar (Binder (mkNum (str "minor") q)) t
        k ps cVars eVars

  (recTys, recRls) <- runE "internal: deriving the block's recursors: "
                           envC recLps $ withRecCtx $ \ps cVars eVars -> do
    tys <- forM [0 .. n - 1] $ \i -> do
      (is, _) <- openArity ctxt nps ps (cmArity (members !! i))
      z <- freshFVar (bnd "t") (mkApps (Const (memNames !! i) selfL)
                                       (map FVar ps ++ map FVar is))
      concl <- closePis (is ++ [z]) (mkApps (FVar (cVars !! i))
                                            (map FVar is ++ [FVar z]))
      closePis (ps ++ cVars ++ eVars) concl
    rls <- forM [0 .. n - 1] $ \i ->
      forM (zip3 [0 ..] (ctorsOf i) (occs !! i)) $ \(k, (cn, cty), fs) ->
        openCtor ctxt nps ps cty (length fs) $ \bs _ -> do
          ihs <- forM (recFields fs) $ \(r, j, _) ->
            peelOcc nps (bs !! r) $ \ys pir ->
              closeLams ys (mkApps (Const (recNameOf j) recUs)
                (map FVar ps ++ map FVar cVars ++ map FVar eVars ++ pir
                 ++ [mkApps (FVar (bs !! r)) (map FVar ys)]))
          rhs <- closeLams (ps ++ cVars ++ eVars ++ bs)
                   (mkApps (FVar (eVars !! absCtor i k)) (map FVar bs ++ ihs))
          pure RecRule { rrCtor = cn, rrNumFields = length fs, rrRhs = rhs }
    pure (tys, rls)

  let recInfos =
        [ RecInfo { recName       = recNameOf i
                  , recLevels     = recLps
                  , recType       = recTys !! i
                  , recInduct     = memNames !! i
                  , recNumParams  = nps
                  , recNumMotives = n
                  , recNumIndices = nIdxs !! i
                  , recNumMinors  = sum nCtors
                  , recRules      = recRls !! i
                  , recK          = False
                  }
        | i <- [0 .. n - 1] ]
      recDef i v = CDef DefInfo { defName = recNameOf i, defLevels = recLps
                                , defType = recTys !! i, defValue = v
                                , defHint = HAbbrev }

  -- A @Prop@ member's recursor recurses over the shadow.  Its shadow motives
  -- send a @Prop@ member to the motive it was given and a data member to
  -- @Sig (t_j a) (C_j a)@ -- a proposition saying \"there is a @t_j@ here, and
  -- the motive holds of it\" -- and its shadow minor premises take the pair
  -- apart again wherever the block's own minor premise wants the data value.
  -- The pair never leaves @Prop@, so no proof is eliminated into data.
  propVals <- runE "internal: deriving a proposition's recursor: "
                   envC recLps $ withRecCtx $ \ps cVars eVars -> do
    let sigLs j = [resLvls !! j, elimLvl j]
    motives <- forM [0 .. n - 1] $ \j ->
      if isProp j then pure (FVar (cVars !! j)) else do
        (is, _) <- openArity ctxt nps ps (cmArity (members !! j))
        w <- freshFVar (bnd "t") (mkApps (Const (shTy j) selfL)
                                         (map FVar ps ++ map FVar is))
        closeLams (is ++ [w]) (mkApps (Const sigTy (sigLs j))
          [ mkApps (Const (memNames !! j) selfL) (map FVar ps ++ map FVar is)
          , mkApps (FVar (cVars !! j)) (map FVar is) ])
    forM propIs $ \i -> do
      let sr = cbRecs shb !! i
      mts <- minorTelescope ctxt nps ps sr selfL motives
      es <- forM (zip mts [ (q, k) | q <- [0 .. n - 1]
                                   , k <- [0 .. nCtors !! q - 1] ]) $
        \((_, mt), (q, k)) -> do
          let fs  = occs !! q !! k
              nf  = length fs
              nih = length (recFields fs)
          tele <- teleOfPis ctxt (nf + nih) mt
          withLocals tele $ \xs -> do
            let (fvs, ihvs) = splitAt nf xs
            ridx <- resultIndices nps (mkApps (Const (shCtorN q k) selfL)
                                              (map FVar ps ++ map FVar fvs))
            -- One @Sig.rec@ per field that points at a data member: it binds the
            -- value the shadow threw away and the motive proof beside it.
            pairs <- forM [ (r, j) | (r, j, _) <- recFields fs, not (isProp j) ] $
              \(r, j) -> do
                pir <- resultIndices nps (FVar (fvs !! r))
                let alpha = mkApps (Const (memNames !! j) selfL)
                                   (map FVar ps ++ pir)
                    beta  = mkApps (FVar (cVars !! j)) pir
                b  <- freshFVar (bnd "val") alpha
                pf <- freshFVar (bnd "ih") (mkApps beta [FVar b])
                pure (r, j, alpha, beta, b, pf)
            let valOf r = case [ b | (r', _, _, _, b, _) <- pairs, r' == r ] of
                            (b : _) -> FVar b
                            []      -> FVar (fvs !! r)
                ihOf r  = case [ p | (r', _, _, _, _, p) <- pairs, r' == r ] of
                            (p : _) -> FVar p
                            []      -> FVar (ihvs !! ihIdx (/= Nothing) fs r)
                fields  = map valOf [0 .. nf - 1]
                core    = mkApps (FVar (eVars !! absCtor q k))
                            (fields ++ [ ihOf r | (r, _, _) <- recFields fs ])
                ctorApp = mkApps (Const (fst (ctorsOf q !! k)) selfL)
                                 (map FVar ps ++ fields)
                target
                  | isProp q  = mkApps (FVar (cVars !! q))
                      (ridx ++ [mkApps (Const (shCtorN q k) selfL)
                                       (map FVar ps ++ map FVar fvs)])
                  | otherwise = mkApps (Const sigTy (sigLs q))
                      [ mkApps (Const (memNames !! q) selfL) (map FVar ps ++ ridx)
                      , mkApps (FVar (cVars !! q)) ridx ]
                body0
                  | isProp q  = core
                  | otherwise = mkApps (Const sigMk (sigLs q))
                      [ mkApps (Const (memNames !! q) selfL) (map FVar ps ++ ridx)
                      , mkApps (FVar (cVars !! q)) ridx, ctorApp, core ]
            body <- foldM (\acc (r, j, alpha, beta, b, pf) -> do
                      s <- freshFVar (bnd "pair")
                             (mkApps (Const sigTy (sigLs j)) [alpha, beta])
                      mot <- closeLams [s] target
                      arm <- closeLams [b, pf] acc
                      pure (mkApps (Const sigRec (sigLs j))
                              [alpha, beta, mot, arm, FVar (ihvs !! ihIdx (/= Nothing) fs r)]))
                    body0 pairs
            closeLams xs body
      closeLams (ps ++ cVars ++ eVars)
        (mkApps (Const (shRecN i) selfL) (map FVar ps ++ motives ++ es))

  envP <- foldM (\env (i, v) -> do
                   runE_ ("the recursor of " ++ showName (memNames !! i)
                          ++ " is not the one its all-Prop shadow justifies: ")
                         env recLps (checkType v (recTys !! i))
                   addConst env (recDef i v))
                envC (zip propIs propVals)

  -- A data member's recursor recurses over its own component.  The component's
  -- motives are the block's, unchanged; a field into the same component brings
  -- its induction hypothesis with it, and every other recursive field -- into a
  -- proposition, or into a component already declared -- gets one by calling
  -- that member's recursor, which is why these go in component order.
  (envDef, dataVals) <- foldM
    (\(env, acc) q -> do
      dr <- drOf q
      let sc  = sccOf q
          big = length (recLevels dr) > length lvls
          us  = [ elimLvl q | big ] ++ selfL
      unless (big || not (isDefinitelyNonZero (resLvls !! q))) $
        Left (ctxt ++ "internal: the component of " ++ showName (memNames !! q)
              ++ " lost its large elimination")
      v <- runE ("internal: deriving the recursor of " ++ showName (memNames !! q)
                 ++ ": ") env recLps $ withRecCtx $ \ps cVars eVars -> do
        let motives = [ FVar (cVars !! s) | s <- sc ]
        mts <- minorTelescope ctxt nps ps dr us motives
        gs <- forM (zip mts [ (s, k) | s <- sc, k <- [0 .. nCtors !! s - 1] ]) $
          \((_, mt), (s, k)) -> do
            let fs   = occs !! s !! k
                nf   = length fs
                same = \o -> case o of Just (j, _) -> j `elem` sc; Nothing -> False
                nih  = length (filter same fs)
            tele <- teleOfPis ctxt (nf + nih) mt
            withLocals tele $ \xs -> do
              let (fvs, ihvs) = splitAt nf xs
              ihs <- forM (recFields fs) $ \(r, j, _) ->
                if j `elem` sc then pure (FVar (ihvs !! ihIdx same fs r))
                else peelOcc nps (fvs !! r) $ \ys pir ->
                  closeLams ys (mkApps (Const (recNameOf j) recUs)
                    (map FVar ps ++ map FVar cVars ++ map FVar eVars ++ pir
                     ++ [mkApps (FVar (fvs !! r)) (map FVar ys)]))
              closeLams xs (mkApps (FVar (eVars !! absCtor s k))
                                   (map FVar fvs ++ ihs))
        closeLams (ps ++ cVars ++ eVars)
          (mkApps (Const (drName q) us) (map FVar ps ++ motives ++ gs))
      runE_ ("the recursor of " ++ showName (memNames !! q) ++ " is not the one \
             \its data component justifies: ")
            env recLps (checkType v (recTys !! q))
      env' <- addConst env (recDef q v)
      pure (env', acc ++ [(q, v)]))
    (envP, []) (concat sccs)

  --------------------------------------------------- 9. the iota rules hold.
  -- Everything above is a construction; this is the check that the construction
  -- computes.  In an environment where /every/ recursor is still a definition --
  -- so the reduction has to go through the derivation rather than through the
  -- rule being checked -- each rule's left-hand side is inferred, its right-hand
  -- side is checked at that type, and the two are compared.  Only then is a data
  -- member's recursor turned into a primitive with that rule attached.
  forM_ [0 .. n - 1] $ \i ->
    runE_ ("the reduction rules of " ++ showName (recNameOf i)
           ++ " are not the ones its derivation computes: ")
          envDef recLps $ withRecCtx $ \ps cVars eVars ->
      forM_ (zip3 [0 ..] (ctorsOf i) (occs !! i)) $ \(k, (cn, cty), fs) ->
        openCtor ctxt nps ps cty (length fs) $ \bs _ -> do
          let pre = map FVar ps ++ map FVar cVars ++ map FVar eVars
              maj = mkApps (Const cn selfL) (map FVar ps ++ map FVar bs)
          ridx <- resultIndices nps maj
          let lhs = mkApps (Const (recNameOf i) recUs) (pre ++ ridx ++ [maj])
              rhs = instLams (pre ++ map FVar bs) (rrRhs (recRls !! i !! k))
          want <- infer lhs
          checkType rhs want
          ok <- isDefEq lhs rhs
          unless ok $ throwTC (showName cn ++ ": " ++ showExpr lhs
                               ++ "\n  does not reduce to " ++ showExpr rhs)

  ---------------------------------------------------- 10. the final environment.
  -- The @Prop@ members' recursors stay definitions, and have to: their major
  -- premises are definitions too, so a primitive recursor's iota rule could
  -- never fire on one, while a definition unfolds into the shadow's recursor and
  -- the genuine iota rule underneath it.  Nothing is lost -- every application
  -- of one is a proof, and proof irrelevance decides those anyway.
  envFinal <- foldM addConst envP [ CRec (recInfos !! q) | (q, _) <- dataVals ]
  forM_ dataVals $ \(q, _) -> checkRecRules envFinal (recInfos !! q)
  forM_ [0 .. n - 1] $ \i ->
    case find ((== recNameOf i) . exrName) recs of
      Nothing -> Left ("no exported recursor named " ++ showName (recNameOf i))
      Just rv -> checkRecursorMatches envFinal memNames rv (recInfos !! i)

  pure BlockResult
    { brEnv     = envFinal
    , brIndices = nIdxs
    , brFields  = map (map length) occs
    , brRec     = cbRec shb
    , brRefl    = cbRefl shb
    }

-- Small pieces ----------------------------------------------------------------

-- | Rename constants wholesale, leaving their universe arguments alone.
--
-- A @Proj@'s type name is deliberately /not/ renamed: a member of a block being
-- declared is not a structure yet, so a projection out of one could not have
-- typechecked, and rewriting it would only make the shadow accept something the
-- block does not have.
renameConsts :: [(Name, Name)] -> Expr -> Expr
renameConsts tbl = go
  where
    go e = case e of
      Const c us  -> maybe e (\c' -> Const c' us) (lookup c tbl)
      App f a     -> App (go f) (go a)
      Lam b t v   -> Lam b (go t) (go v)
      Pi  b t v   -> Pi  b (go t) (go v)
      Let b t v w -> Let b (go t) (go v) (go w)
      Proj t i s  -> Proj t i (go s)
      _           -> e

-- | Classify every field of a constructor: which member of the block, if any,
-- it recurses into, and whether it does so under binders.
--
-- Run once, with the members held as axioms, and reused for all three views of
-- the block.  It is not the positivity check -- that is the shadow's flattening,
-- which runs first and is the code the corpus exercises -- but it repeats enough
-- of it to be sure that what it reports is what the core saw.
scanCtor :: String -> [Name] -> [Level] -> [Int] -> Int -> [Int] -> Int -> Expr
         -> TC [FieldOcc]
scanCtor ctx memNames selfL nIdxs nps ps self cty =
  peelSharedParams ctx nps ps cty >>= go []
  where
    occurs e = any (`occursConst` e) memNames
    go acc ty = whnf ty >>= \case
      Pi b dom cod -> do
        o <- classify dom
        x <- freshFVar b dom
        go (o : acc) (inst1 (FVar x) cod)
      res -> do
        (j, _) <- splitMem "the result type" res
        unless (j == self) $
          throwTC (ctx ++ "a constructor must produce the member it belongs to")
        pure (reverse acc)
    classify dom0
      | not (occurs dom0) = pure Nothing
      | otherwise = do
          dom <- whnf dom0
          if occurs dom then peel [] dom else pure Nothing
    peel xs t = whnf t >>= \case
      Pi b dom cod -> do
        when (occurs dom) $ do
          d <- whnf dom
          when (occurs d) $ throwTC
            (ctx ++ "a member of the block occurs to the left of an arrow in one \
                    \of its constructor's fields")
        x <- freshFVar b dom
        peel (x : xs) (inst1 (FVar x) cod)
      res -> do
        (j, _) <- splitMem "a constructor field" res
        pure (Just (j, not (null xs)))
    splitMem what res = case unApps res of
      (Const c us, as) | Just j <- elemIndex c memNames -> do
        unless (length us == length selfL && and (zipWith levelEquiv us selfL)) $
          throwTC (ctx ++ what ++ " uses " ++ showName c
                   ++ " at universes other than the block's own")
        unless (length as == nps + nIdxs !! j) $
          throwTC (ctx ++ what ++ ": " ++ showName c ++ " is not fully applied")
        unless (take nps as == map FVar ps) $
          throwTC (ctx ++ what ++ " does not use the block's own parameters")
        let ixs = drop nps as
        forM_ ixs $ \a -> when (occurs a) $
          throwTC (ctx ++ "a member of the block occurs in an index of " ++ what)
        pure (j, ixs)
      _ -> throwTC (ctx ++ what ++ " must be a member of the block applied to its \
                    \own parameters and indices, but is " ++ showExpr res
                    ++ "; a nested occurrence in a heterogeneous block is not \
                       \supported")

-- | Open a constructor's fields past the block's parameters, and report the
-- index arguments its result type is applied to.
openCtor :: String -> Int -> [Int] -> Expr -> Int -> ([Int] -> [Expr] -> TC a) -> TC a
openCtor ctx nps ps cty nf k = peelSharedParams ctx nps ps cty >>= go nf []
  where
    go 0 acc ty = do
      res <- whnf ty
      k (reverse acc) (drop nps (snd (unApps res)))
    go i acc ty = whnf ty >>= \case
      Pi b dom cod -> do
        x <- freshFVar b dom
        go (i - 1) (x : acc) (inst1 (FVar x) cod)
      _ -> throwTC (ctx ++ "internal: a constructor lost a field")

-- | Take a recursive field apart: the binders it lies under, and the index
-- arguments the member it ends in is applied to.
peelOcc :: Int -> Int -> ([Int] -> [Expr] -> TC a) -> TC a
peelOcc nps x k = localType x >>= go []
  where
    go acc t = whnf t >>= \case
      Pi b dom cod -> do
        y <- freshFVar b dom
        go (y : acc) (inst1 (FVar y) cod)
      res -> k (reverse acc) (drop nps (snd (unApps res)))

-- | The index arguments of a term's type.
resultIndices :: Int -> Expr -> TC [Expr]
resultIndices nps e = do
  t <- whnf =<< infer e
  pure (drop nps (snd (unApps t)))

-- | The minor premises of a derived recursor, as a telescope, with its
-- parameters opened against @ps@ and its motives already instantiated.
--
-- Reading the binders off the recursor rather than rebuilding them is what
-- makes the adapters below independent of how "Kernel.Inductive" chose to write
-- an induction hypothesis down.
minorTelescope :: String -> Int -> [Int] -> RecInfo -> [Level] -> [Expr]
               -> TC [(Binder, Expr)]
minorTelescope ctx nps ps r us motives = do
  unless (length motives == recNumMotives r) $
    throwTC (ctx ++ "internal: " ++ showName (recName r) ++ " wants "
             ++ show (recNumMotives r) ++ " motives")
  rest <- peelSharedParams ctx nps ps (instLevelsE (recLevels r) us (recType r))
  after <- instPis motives rest
  teleOfPis ctx (recNumMinors r) after

-- | Peel leading @Pi@s, substituting the given arguments as we go.
instPis :: [Expr] -> Expr -> TC Expr
instPis []       t = pure t
instPis (a : as) t = case t of
  Pi _ _ cod -> instPis as (inst1 a cod)
  _          -> throwTC "internal: too few binders to instantiate"

-- | The first @k@ binders of a @Pi@ telescope.
teleOfPis :: String -> Int -> Expr -> TC [(Binder, Expr)]
teleOfPis ctx k t = do
  let (tele, _) = unPisN k t
  unless (length tele == k) $
    throwTC (ctx ++ "internal: a derived type has fewer binders than it should")
  pure tele
