{-# LANGUAGE BangPatterns     #-}
{-# LANGUAGE MagicHash        #-}
{-# LANGUAGE PatternSynonyms  #-}
-- | Core expressions.
--
-- This is the /whole/ term language the kernel checks.  Compared with the
-- export format it has lost: binder annotations (@implicit@ &c.) and @mdata@,
-- both of which are elaboration hints with no logical content.  See SPEC.md.
--
-- Representation is locally nameless: bound variables are de Bruijn indices,
-- and a binder that has been entered is replaced by an 'FVar' carrying a unique
-- id whose type lives in the local context.  'FVar' never occurs in a term
-- stored in the environment; it exists only inside the checker.
--
-- A term is a /graph/, not a tree.  The export format shares subterms, and so
-- do 'liftE', 'instN' and 'instLevelsE'; a term whose printed form is
-- astronomically large routinely fits in a few thousand nodes.  Two caches keep
-- the kernel working on the graph rather than on its unfolding:
--
-- * every node that can contain a bound variable caches its 'looseBVarRange',
--   so the de Bruijn plumbing can leave a closed subterm alone in constant time
--   instead of rebuilding it;
--
-- * every node caches a structural hash, which decides most inequalities in
--   constant time and gives 'Kernel.Check' something to key a memo table on.
--
-- Both caches are maintained by pattern synonyms: the constructors 'App',
-- 'Lam', ... below compute them, and matching on them ignores them, so the rest
-- of the kernel reads as if @Expr@ were a plain tree.  Nothing outside this
-- module may see the underlying constructors, or a cache could be set to a lie.
module Kernel.Expr
  ( Expr
  , pattern BVar, pattern FVar, pattern Sort, pattern Const, pattern App
  , pattern Lam, pattern Pi, pattern Let, pattern Proj
  , pattern NatLit, pattern StrLit
  , Binder (..)
  , exprHash
  , ptrEq
  -- * Construction
  , mkApps, unApps, unAppsN, headOf
  , mkPis, mkLams, unPis, unPisN, unLamsN
  , mkArrow
  -- * de Bruijn plumbing
  , liftE
  , instN
  , inst1
  -- * Local constants
  , abstractFVars
  , instantiateBody
  -- * Queries
  , hasLooseBVars
  , looseBVarRange
  , occursConst
  , constsOf
  , instLevelsE
  , showExpr
  ) where

import           Control.Monad.ST      (ST, runST)
import qualified Data.ByteString.Char8 as B
import           Data.IntMap.Strict    (IntMap)
import qualified Data.IntMap.Strict    as IM
import           Data.STRef            (STRef, modifySTRef', newSTRef, readSTRef)
import qualified Data.Set              as S
import           GHC.Exts              (isTrue#, reallyUnsafePtrEquality#)
import           Kernel.Level
import           Kernel.Name

-- | Are these two values the same heap object?
--
-- One-sided: @True@ means the arguments are literally the same thing, @False@
-- means nothing at all.  Used only to take a shortcut that a slower structural
-- test would reach anyway, so a spurious @False@ costs time and never changes
-- an answer.
ptrEq :: a -> a -> Bool
ptrEq x y = isTrue# (reallyUnsafePtrEquality# x y)
{-# INLINE ptrEq #-}

-- | A binder's display name.  Cosmetic; never affects checking.
newtype Binder = Binder Name
  deriving (Eq, Ord)

instance Show Binder where show (Binder n) = showName n

-- | The real representation.  @X@-prefixed constructors are private.  Where
-- two @Int@s appear they are, in order, the cached hash and the cached
-- 'looseBVarRange'; a node with only one carries the hash.
data Expr
  = XBVar !Int                                  -- ^ de Bruijn index
  | XFVar !Int                                  -- ^ local constant (checker-internal)
  | XSort !Int !Level
  | XConst !Int !Name ![Level]
  | XApp !Int !Int !Expr !Expr
  | XLam !Int !Int !Binder !Expr !Expr          -- ^ @fun (x : t) => b@
  | XPi  !Int !Int !Binder !Expr !Expr          -- ^ @(x : t) -> b@
  | XLet !Int !Int !Binder !Expr !Expr !Expr    -- ^ @let x : t := v; b@
  | XProj !Int !Int !Name !Int !Expr            -- ^ @s.i@ at structure type @T@ (0-based)
  | XNatLit !Int !Integer                       -- ^ abbreviation for a @Nat.succ@ tower
  | XStrLit !Int !B.ByteString                  -- ^ abbreviation for @String.mk [...]@

-- | Smallest @k@ such that no @BVar i@ with @i >= k@ occurs free.  Constant
-- time: it is either immediate or cached.
looseBVarRange :: Expr -> Int
looseBVarRange e = case e of
  XBVar i          -> i + 1
  XApp _ r _ _     -> r
  XLam _ r _ _ _   -> r
  XPi  _ r _ _ _   -> r
  XLet _ r _ _ _ _ -> r
  XProj _ r _ _ _  -> r
  _                -> 0

-- | A hash of the node's structure.  Constant time.
--
-- Equal terms hash equally; unequal terms usually do not.  Binder names are
-- left out deliberately -- they are cosmetic, and a hash is allowed to be
-- coarser than the equality it accompanies, never finer.
exprHash :: Expr -> Int
exprHash e = case e of
  XBVar i          -> hashMix 2 i
  XFVar i          -> hashMix 4 i
  XSort h _        -> h
  XConst h _ _     -> h
  XApp h _ _ _     -> h
  XLam h _ _ _ _   -> h
  XPi  h _ _ _ _   -> h
  XLet h _ _ _ _ _ -> h
  XProj h _ _ _ _  -> h
  XNatLit h _      -> h
  XStrLit h _      -> h

-- | Structural equality, with the two caches doing the work.
--
-- The pointer test is what makes comparing shared subterms affordable: an
-- exported term is a graph, and its tree unfolding can be exponentially larger.
-- The hash test then settles almost every remaining pair at the root.
instance Eq Expr where
  a == b = ptrEq a b || (exprHash a == exprHash b && eqE a b)

-- | Equality below the root, for two terms whose hashes already agree.
--
-- Same shape as 'instN', and for the same reason. The plain recursion compares a
-- shared pair of subterms once per /path/ that reaches it, and a term produced
-- by unfolding a @brecOn@ has exponentially more paths than nodes; two such
-- terms that really are equal are then the worst case, because nothing
-- short-circuits. So the plain recursion runs under a visit budget and a
-- memoised traversal takes over when that runs out. The budget is the detector:
-- below it there is no sharing worth a table, and a comparison that exceeds it
-- has nothing else that could be taking the time.
--
-- Only equal pairs are remembered, which is all that is needed: a @False@
-- anywhere propagates through the conjunctions to the root, so no pair is ever
-- asked about twice after answering @False@.
eqE :: Expr -> Expr -> Bool
eqE a0 b0 = case plain eqBudget a0 b0 of
    (r, k) | k >= 0 -> r
    _               -> runST (newSTRef IM.empty >>= \ref -> go ref a0 b0)
  where
    plain :: Int -> Expr -> Expr -> (Bool, Int)
    plain !k x y
      | k < 0                    = (False, k)
      | ptrEq x y                = (True, k)
      | exprHash x /= exprHash y = (False, k)
      | otherwise = case (x, y) of
          (XApp _ _ f a, XApp _ _ g b) -> two (k - 1) f g a b
          (XLam _ _ n t b, XLam _ _ n' t' b')
            | n == n'   -> two (k - 1) t t' b b'
          (XPi _ _ n t b, XPi _ _ n' t' b')
            | n == n'   -> two (k - 1) t t' b b'
          (XLet _ _ n t v b, XLet _ _ n' t' v' b')
            | n == n'   -> case two (k - 1) t t' v v' of
                (True, k1) -> plain k1 b b'
                r          -> r
          (XProj _ _ s i b, XProj _ _ s' i' b')
            | i == i', s == s' -> plain (k - 1) b b'
          _ -> (eqLeaf x y, k - 1)

    two !k f g a b = case plain k f g of
      (True, k1) -> plain k1 a b
      r          -> r

    go :: STRef s (IntMap [(Expr, Expr)]) -> Expr -> Expr -> ST s Bool
    go ref x y
      | ptrEq x y                = pure True
      | exprHash x /= exprHash y = pure False
      | otherwise = do
          m <- readSTRef ref
          if seen (IM.findWithDefault [] (exprHash x) m) then pure True else do
            r <- kids ref x y
            if not r then pure False else do
              modifySTRef' ref (IM.insertWith (++) (exprHash x) [(x, y)])
              pure True
      where
        seen ((p, q) : rest) = (ptrEq p x && ptrEq q y) || seen rest
        seen []              = False

    kids ref x y = case (x, y) of
      (XApp _ _ f a, XApp _ _ g b) -> andM (go ref f g) (go ref a b)
      (XLam _ _ n t b, XLam _ _ n' t' b')
        | n == n' -> andM (go ref t t') (go ref b b')
      (XPi _ _ n t b, XPi _ _ n' t' b')
        | n == n' -> andM (go ref t t') (go ref b b')
      (XLet _ _ n t v b, XLet _ _ n' t' v' b')
        | n == n' -> andM (go ref t t') (andM (go ref v v') (go ref b b'))
      (XProj _ _ s i b, XProj _ _ s' i' b')
        | i == i', s == s' -> go ref b b'
      _ -> pure (eqLeaf x y)

    andM p q = p >>= \r -> if r then q else pure False

-- | The cases with no subterms to recur into.  Reached from 'eqE' only, where
-- the two hashes are known to agree.
eqLeaf :: Expr -> Expr -> Bool
eqLeaf (XBVar i)     (XBVar j)     = i == j
eqLeaf (XFVar i)     (XFVar j)     = i == j
eqLeaf (XSort _ l)   (XSort _ m)   = l == m
eqLeaf (XConst _ n ls) (XConst _ m ms) = n == m && ls == ms
eqLeaf (XNatLit _ x) (XNatLit _ y) = x == y
eqLeaf (XStrLit _ x) (XStrLit _ y) = x == y
eqLeaf _             _             = False

-- | How many pairs of nodes 'eqE' may compare before it is worth a memo table.
--
-- Larger than 'instBudget' because equality, unlike substitution, is asked about
-- whole declared types and stored bodies as often as it is asked about the small
-- open terms conversion produces, and because the work thrown away on a miss is
-- a walk that allocates nothing.
eqBudget :: Int
eqBudget = 1024

-- | Some total order agreeing with '=='.  Not alphabetical, not structural:
-- hash first, which is fine because nothing reads an ordering on terms for
-- anything but keying a container.
instance Ord Expr where
  compare a b
    | ptrEq a b = EQ
    | otherwise = case compare (exprHash a) (exprHash b) of
        EQ -> cmpE a b
        o  -> o

cmpE :: Expr -> Expr -> Ordering
cmpE a b = case compare (tagE a) (tagE b) of
  EQ -> fields a b
  o  -> o
  where
    fields (XBVar i)          (XBVar j)          = compare i j
    fields (XFVar i)          (XFVar j)          = compare i j
    fields (XSort _ l)        (XSort _ m)        = compare l m
    fields (XConst _ n ls)    (XConst _ m ms)    = compare (n, ls) (m, ms)
    fields (XApp _ _ f x)     (XApp _ _ g y)     = compare f g <> compare x y
    fields (XLam _ _ n t x)   (XLam _ _ m u y)   =
      compare n m <> compare t u <> compare x y
    fields (XPi _ _ n t x)    (XPi _ _ m u y)    =
      compare n m <> compare t u <> compare x y
    fields (XLet _ _ n t v x) (XLet _ _ m u w y) =
      compare n m <> compare t u <> compare v w <> compare x y
    fields (XProj _ _ s i x)  (XProj _ _ r j y)  =
      compare s r <> compare i j <> compare x y
    fields (XNatLit _ x)      (XNatLit _ y)      = compare x y
    fields (XStrLit _ x)      (XStrLit _ y)      = compare x y
    fields _                  _                  = EQ   -- tags agree

tagE :: Expr -> Int
tagE e = case e of
  XBVar{} -> 0; XFVar{} -> 1; XSort{} -> 2; XConst{} -> 3; XApp{} -> 4
  XLam{}  -> 5; XPi{}   -> 6; XLet{}  -> 7; XProj{}  -> 8; XNatLit{} -> 9
  XStrLit{} -> 10

hasLooseBVars :: Expr -> Bool
hasLooseBVars e = looseBVarRange e > 0

-- | Range of a binder's body seen from outside the binder.
under :: Expr -> Int
under b = max 0 (looseBVarRange b - 1)

-- | Combine child hashes under a per-constructor seed.
h1 :: Int -> Int -> Int
h1 seed x = hashMix seed x

h2 :: Int -> Int -> Int -> Int
h2 seed x y = hashMix (hashMix seed x) y

h3 :: Int -> Int -> Int -> Int -> Int
h3 seed x y z = hashMix (hashMix (hashMix seed x) y) z

pattern BVar :: Int -> Expr
pattern BVar i = XBVar i

pattern FVar :: Int -> Expr
pattern FVar i = XFVar i

pattern Sort :: Level -> Expr
pattern Sort l <- XSort _ l
  where Sort l = XSort (h1 13 (levelHash l)) l

pattern Const :: Name -> [Level] -> Expr
pattern Const n ls <- XConst _ n ls
  where Const n ls = XConst (foldl (\h l -> hashMix h (levelHash l))
                                   (h1 19 (nameHash n)) ls) n ls

pattern NatLit :: Integer -> Expr
pattern NatLit n <- XNatLit _ n
  where NatLit n = XNatLit (h1 23 (fromInteger n)) n

pattern StrLit :: B.ByteString -> Expr
pattern StrLit s <- XStrLit _ s
  where StrLit s = XStrLit (h1 29 (B.foldl' (\h c -> h * 33 + fromEnum c) 5381 s)) s

pattern App :: Expr -> Expr -> Expr
pattern App f a <- XApp _ _ f a
  where App f a = XApp (h2 31 (exprHash f) (exprHash a))
                       (max (looseBVarRange f) (looseBVarRange a)) f a

pattern Lam :: Binder -> Expr -> Expr -> Expr
pattern Lam n t b <- XLam _ _ n t b
  where Lam n t b = XLam (h2 37 (exprHash t) (exprHash b))
                         (max (looseBVarRange t) (under b)) n t b

pattern Pi :: Binder -> Expr -> Expr -> Expr
pattern Pi n t b <- XPi _ _ n t b
  where Pi n t b = XPi (h2 41 (exprHash t) (exprHash b))
                       (max (looseBVarRange t) (under b)) n t b

pattern Let :: Binder -> Expr -> Expr -> Expr -> Expr
pattern Let n t v b <- XLet _ _ n t v b
  where Let n t v b =
          XLet (h3 43 (exprHash t) (exprHash v) (exprHash b))
               (max (looseBVarRange t) (max (looseBVarRange v) (under b))) n t v b

pattern Proj :: Name -> Int -> Expr -> Expr
pattern Proj s i b <- XProj _ _ s i b
  where Proj s i b = XProj (h3 47 (nameHash s) i (exprHash b))
                           (looseBVarRange b) s i b

{-# COMPLETE BVar, FVar, Sort, Const, App, Lam, Pi, Let, Proj, NatLit, StrLit #-}

instance Show Expr where show = showExpr

-- Construction ----------------------------------------------------------------

mkApps :: Expr -> [Expr] -> Expr
mkApps = foldl App

-- | Split off a spine: @unApps (f a b) == (f, [a, b])@.
unApps :: Expr -> (Expr, [Expr])
unApps = go []
  where go acc (App f a) = go (a : acc) f
        go acc e         = (e, acc)

-- | The head of a spine, without building the list of arguments.
--
-- @fst . unApps@ says the same thing and allocates a cons cell per argument to
-- do it.  Several of the hottest questions the checker asks -- is this head a
-- definition, what is the conclusion of this telescope -- want only the head.
headOf :: Expr -> Expr
headOf (App f _) = headOf f
headOf e         = e

-- | Like 'unApps' but keeps at most @n@ arguments, leaving the rest applied to
-- the head.  Used when a spine is longer than a reduction rule expects.
unAppsN :: Int -> Expr -> (Expr, [Expr])
unAppsN n e =
  let (h, as) = unApps e
      k       = length as - n
  in if k <= 0 then (h, as) else (mkApps h (take k as), drop k as)

mkPis :: [(Binder, Expr)] -> Expr -> Expr
mkPis tele body = foldr (\(n, t) acc -> Pi n t acc) body tele

mkLams :: [(Binder, Expr)] -> Expr -> Expr
mkLams tele body = foldr (\(n, t) acc -> Lam n t acc) body tele

-- | Peel every leading @Pi@ (no reduction).
unPis :: Expr -> ([(Binder, Expr)], Expr)
unPis (Pi n t b) = let (tele, r) = unPis b in ((n, t) : tele, r)
unPis e          = ([], e)

-- | Peel exactly @n@ leading @Pi@s, or fewer if the term runs out.
unPisN :: Int -> Expr -> ([(Binder, Expr)], Expr)
unPisN 0 e          = ([], e)
unPisN k (Pi n t b) = let (tele, r) = unPisN (k - 1) b in ((n, t) : tele, r)
unPisN _ e          = ([], e)

unLamsN :: Int -> Expr -> ([(Binder, Expr)], Expr)
unLamsN 0 e           = ([], e)
unLamsN k (Lam n t b) = let (tele, r) = unLamsN (k - 1) b in ((n, t) : tele, r)
unLamsN _ e           = ([], e)

-- | Non-dependent function type.
mkArrow :: Expr -> Expr -> Expr
mkArrow a b = Pi (Binder anon) a (liftE 0 1 b)

-- Memoised traversal ----------------------------------------------------------

-- | A memo table for one traversal of one term, keyed on a node and the binder
-- depth it is visited at.
--
-- Why every traversal below needs one: a term is a graph, and a plain recursion
-- visits a shared node once per /path/ to it.  With sharing that is
-- exponentially more often than the node exists.  Memoising on the node makes
-- each traversal linear in the graph -- and, just as importantly, makes the
-- /result/ a graph too, since the same answer node is handed to every parent
-- instead of a fresh copy.
--
-- Nodes are matched by 'ptrEq' rather than '=='.  Structural equality is what
-- we are trying not to pay for; a miss on a structurally-equal-but-distinct
-- node only costs the recomputation we would have done anyway.
-- | One slot per hash: a collision evicts rather than chains.
--
-- These tables are built and thrown away once per traversal, and every entry in
-- them costs an insertion into the map.  Chaining would make a lookup complete
-- -- it would find an entry whenever one exists -- but a memo does not have to
-- be complete to be correct, only to be right when it answers.  Since a miss
-- costs a recomputation and a hash collision between two nodes reached in the
-- same traversal is rare, one slot per hash is the better trade, and it is the
-- allocation of the chain that it saves.
type Memo s a = STRef s (IntMap (Expr, Int, a))

newMemo :: ST s (Memo s a)
newMemo = newSTRef IM.empty

memoAt :: Memo s a -> Int -> Expr -> ST s a -> ST s a
memoAt ref d ex mk = do
  m <- readSTRef ref
  let key = hashMix (exprHash ex) d
  case IM.lookup key m of
    Just (k, d', r) | d == d', ptrEq k ex -> pure r
    _ -> do
      r <- mk
      modifySTRef' ref (IM.insert key (ex, d, r))
      pure r

-- | How many nodes a level substitution may visit before it is worth a memo
-- table.  Larger than 'instBudget' because the terms are declared types and
-- stored bodies rather than the small open terms beta reduction rewrites.
levelBudget :: Int
levelBudget = 512

-- | How many nodes a substitution may visit before it is worth a memo table.
--
-- Small enough that the work thrown away on a miss is a rounding error, large
-- enough that a table is only built when there is real sharing to exploit.
instBudget :: Int
instBudget = 64

-- de Bruijn plumbing ----------------------------------------------------------

-- | @liftE d k e@ adds @k@ to every bound variable of @e@ with index @>= d@.
--
-- A subterm whose loose variables all sit below @d@ is returned as is, sharing
-- rather than copying.  This is what keeps substitution proportional to the
-- part of the term that actually mentions the variable.
liftE :: Int -> Int -> Expr -> Expr
liftE _ 0 e = e
liftE d0 k e0
  | looseBVarRange e0 <= d0 = e0
  | otherwise = runST (newMemo >>= \ref -> go ref d0 e0)
  where
    go ref d' ex
      | looseBVarRange ex <= d' = pure ex
      | otherwise = memoAt ref d' ex $ case ex of
          BVar i        -> pure (BVar (i + k))   -- @i >= d'@, by the guard
          App f a       -> App <$> go ref d' f <*> go ref d' a
          Lam n t b     -> Lam n <$> go ref d' t <*> go ref (d' + 1) b
          Pi  n t b     -> Pi  n <$> go ref d' t <*> go ref (d' + 1) b
          Let n t v b   -> Let n <$> go ref d' t <*> go ref d' v
                                 <*> go ref (d' + 1) b
          Proj s i b    -> Proj s i <$> go ref d' b
          _             -> pure ex               -- unreachable: range would be 0

-- | @instN vs e@ substitutes @vs !! i@ for @BVar i@ (for @i < length vs@) and
-- lowers the remaining indices by @length vs@.
--
-- Every beta step goes through here, and the great majority of them rewrite a
-- handful of nodes: one bound variable inside the two or three that mention it.
-- Setting up a memo table for that costs more than the substitution.  So the
-- plain recursion is tried first under a visit budget, and the memoised
-- traversal is kept in reserve for the terms that need it -- the ones whose
-- sharing would make the plain recursion exponential, which is exactly what
-- running out of budget detects.  Both compute the same term; only the sharing
-- of the result differs, and below 'instBudget' nodes there is nothing to share.
instN :: [Expr] -> Expr -> Expr
instN [] e = e
instN vs e0
  | looseBVarRange e0 == 0 = e0
  | (r, k) <- plain instBudget 0 e0, k >= 0 = r
  | otherwise = runST (newMemo >>= \ref -> go ref 0 e0)
  where
    n = length vs

    -- Returns the rewritten node and what is left of the budget; a negative
    -- budget means the answer is unfinished and must be thrown away.
    plain !k !d ex
      | k < 0                  = (ex, k)
      | looseBVarRange ex <= d = (ex, k)
      | otherwise = case ex of
          BVar i
            | i < d + n   -> (liftE 0 d (vs !! (i - d)), k')
            | otherwise   -> (BVar (i - n), k')
          App f a       -> let (f', k1) = plain k' d f
                               (a', k2) = plain k1 d a
                           in (App f' a', k2)
          Lam nm t b    -> let (t', k1) = plain k' d t
                               (b', k2) = plain k1 (d + 1) b
                           in (Lam nm t' b', k2)
          Pi  nm t b    -> let (t', k1) = plain k' d t
                               (b', k2) = plain k1 (d + 1) b
                           in (Pi nm t' b', k2)
          Let nm t v b  -> let (t', k1) = plain k' d t
                               (v', k2) = plain k1 d v
                               (b', k3) = plain k2 (d + 1) b
                           in (Let nm t' v' b', k3)
          Proj s i b    -> let (b', k1) = plain k' d b
                           in (Proj s i b', k1)
          _             -> (ex, k')
      where k' = k - 1

    go ref d ex
      -- Nothing at or above @d@ occurs, so there is neither anything to
      -- substitute nor anything to lower.
      | looseBVarRange ex <= d = pure ex
      | otherwise = memoAt ref d ex $ case ex of
          BVar i
            | i < d + n   -> pure (liftE 0 d (vs !! (i - d)))
            | otherwise   -> pure (BVar (i - n))
          App f a       -> App <$> go ref d f <*> go ref d a
          Lam nm t b    -> Lam nm <$> go ref d t <*> go ref (d + 1) b
          Pi  nm t b    -> Pi  nm <$> go ref d t <*> go ref (d + 1) b
          Let nm t v b  -> Let nm <$> go ref d t <*> go ref d v
                                  <*> go ref (d + 1) b
          Proj s i b    -> Proj s i <$> go ref d b
          _             -> pure ex               -- unreachable: range would be 0

-- | Substitute for the outermost bound variable.
inst1 :: Expr -> Expr -> Expr
inst1 v e = instN [v] e

-- | Open a binder body by replacing @BVar 0@ with a local constant.
instantiateBody :: Int -> Expr -> Expr
instantiateBody fid = inst1 (FVar fid)

-- | Close over local constants: @abstractFVars [x0,..,xn-1] e@ turns @xi@ into
-- @BVar (n-1-i)@, i.e. the telescope order in which they were introduced.
abstractFVars :: [Int] -> Expr -> Expr
abstractFVars [] e = e
abstractFVars ids e0 = runST (newMemo >>= \ref -> go ref 0 e0)
  where
    n = length ids
    pos i = lookup i (zip ids [0 ..])
    go ref d ex = case ex of
      FVar i | Just k <- pos i -> pure (BVar (d + n - 1 - k))
             | otherwise       -> pure ex
      BVar _        -> pure ex
      Sort _        -> pure ex
      Const _ _     -> pure ex
      NatLit _      -> pure ex
      StrLit _      -> pure ex
      _             -> memoAt ref d ex $ case ex of
        App f a       -> App <$> go ref d f <*> go ref d a
        Lam nm t b    -> Lam nm <$> go ref d t <*> go ref (d + 1) b
        Pi  nm t b    -> Pi  nm <$> go ref d t <*> go ref (d + 1) b
        Let nm t v b  -> Let nm <$> go ref d t <*> go ref d v
                                <*> go ref (d + 1) b
        Proj s i b    -> Proj s i <$> go ref d b

-- Queries ---------------------------------------------------------------------

occursConst :: Name -> Expr -> Bool
occursConst n e0 = runST (newMemo >>= \ref -> go ref e0)
  where
    go ref ex = case ex of
      Const m _   -> pure (m == n)
      App{}       -> memoAt ref 0 ex (kids ref ex)
      Lam{}       -> memoAt ref 0 ex (kids ref ex)
      Pi{}        -> memoAt ref 0 ex (kids ref ex)
      Let{}       -> memoAt ref 0 ex (kids ref ex)
      Proj{}      -> memoAt ref 0 ex (kids ref ex)
      _           -> pure False
    kids ref ex = anyM (go ref) (children ex)

-- | Every constant a term names.
--
-- @Proj@ carries the structure's name as well as its subterm, and that name is
-- included: it is a reference to a declaration exactly as a 'Const' node is,
-- and a caller asking \"what does this term depend on?\" needs it.
constsOf :: Expr -> S.Set Name
constsOf e0 = runST (newMemo >>= \ref -> go ref e0)
  where
    go ref ex = case ex of
      Const m _   -> pure (S.singleton m)
      App{}       -> memoAt ref 0 ex (kids ref ex)
      Lam{}       -> memoAt ref 0 ex (kids ref ex)
      Pi{}        -> memoAt ref 0 ex (kids ref ex)
      Let{}       -> memoAt ref 0 ex (kids ref ex)
      Proj s _ _  -> memoAt ref 0 ex (S.insert s <$> kids ref ex)
      _           -> pure S.empty
    kids ref ex = S.unions <$> mapM (go ref) (children ex)

-- | The immediate subterms, in no particular order.
children :: Expr -> [Expr]
children ex = case ex of
  App f a     -> [f, a]
  Lam _ t b   -> [t, b]
  Pi  _ t b   -> [t, b]
  Let _ t v b -> [t, v, b]
  Proj _ _ b  -> [b]
  _           -> []

anyM :: Monad m => (a -> m Bool) -> [a] -> m Bool
anyM _ []       = pure False
anyM f (x : xs) = f x >>= \b -> if b then pure True else anyM f xs

-- | Instantiate a declaration's universe parameters throughout a term.
--
-- A subterm that mentions no universe at all -- most of the body of a typical
-- definition or recursor rule -- comes back as the very same node, so it is
-- shared rather than copied.  \"Same node\" is what 'ptrEq' reports on the
-- results, which costs nothing; the alternative of signalling it in a 'Maybe'
-- allocates on every node and measured slower.  Delta and iota both run this on
-- every step, so this is the difference between rebuilding a whole term and
-- rebuilding the path to its @Sort@s and @Const@s.
instLevelsE :: [Name] -> [Level] -> Expr -> Expr
instLevelsE [] _ e = e
instLevelsE ps vs e0
  | (r, k) <- plain levelBudget e0, k >= 0 = r
  | otherwise = runST (newMemo >>= \ref -> go ref e0)
  where
    sub = instLevelParams ps vs

    -- As in 'instN': the plain recursion first, under a budget, because almost
    -- every body this is asked about is a declared type of a few dozen nodes
    -- and building a memo table for it costs more than the walk.  A negative
    -- budget means the answer is unfinished and is thrown away.
    plain !k ex
      | k < 0     = (ex, k)
      | otherwise = case ex of
          Sort l        -> (let l' = sub l in if l' == l then ex else Sort l', k')
          Const _ []    -> (ex, k')
          Const n ls    -> (let ls' = map sub ls
                            in if ls' == ls then ex else Const n ls', k')
          App f a       -> let (f', k1) = plain k' f
                               (a', k2) = plain k1 a
                           in (if ptrEq f f' && ptrEq a a' then ex else App f' a', k2)
          Lam n t b     -> let (t', k1) = plain k' t
                               (b', k2) = plain k1 b
                           in (if ptrEq t t' && ptrEq b b' then ex else Lam n t' b', k2)
          Pi  n t b     -> let (t', k1) = plain k' t
                               (b', k2) = plain k1 b
                           in (if ptrEq t t' && ptrEq b b' then ex else Pi n t' b', k2)
          Let n t v b   -> let (t', k1) = plain k' t
                               (v', k2) = plain k1 v
                               (b', k3) = plain k2 b
                           in (if ptrEq t t' && ptrEq v v' && ptrEq b b'
                                 then ex else Let n t' v' b', k3)
          Proj s i b    -> let (b', k1) = plain k' b
                           in (if ptrEq b b' then ex else Proj s i b', k1)
          _             -> (ex, k')
      where k' = k - 1

    go ref ex = case ex of
      Sort l        -> pure (let l' = sub l in if l' == l then ex else Sort l')
      Const _ []    -> pure ex
      Const n ls    -> pure (let ls' = map sub ls
                             in if ls' == ls then ex else Const n ls')
      App f a       -> memoAt ref 0 ex $ do
                         f' <- go ref f; a' <- go ref a
                         pure (if ptrEq f f' && ptrEq a a' then ex else App f' a')
      Lam n t b     -> memoAt ref 0 ex $ do
                         t' <- go ref t; b' <- go ref b
                         pure (if ptrEq t t' && ptrEq b b' then ex else Lam n t' b')
      Pi  n t b     -> memoAt ref 0 ex $ do
                         t' <- go ref t; b' <- go ref b
                         pure (if ptrEq t t' && ptrEq b b' then ex else Pi n t' b')
      Let n t v b   -> memoAt ref 0 ex $ do
                         t' <- go ref t; v' <- go ref v; b' <- go ref b
                         pure (if ptrEq t t' && ptrEq v v' && ptrEq b b'
                                 then ex else Let n t' v' b')
      Proj s i b    -> memoAt ref 0 ex $ do
                         b' <- go ref b
                         pure (if ptrEq b b' then ex else Proj s i b')
      _             -> pure ex

-- Display ---------------------------------------------------------------------

showExpr :: Expr -> String
showExpr = go (0 :: Int)
  where
    go _ (BVar i)      = "#" ++ show i
    go _ (FVar i)      = "x!" ++ show i
    go _ (Sort l)      = "Sort " ++ showLevel l
    go _ (Const n [])  = showName n
    go _ (Const n ls)  = showName n ++ ".{" ++ commas (map showLevel ls) ++ "}"
    go p e@(App _ _)   = let (h, as) = unApps e
                         in paren (p > 1) (unwords (go 2 h : map (go 2) as))
    go p (Lam n t b)   = paren (p > 0) ("fun (" ++ show n ++ " : " ++ go 0 t ++ ") => " ++ go 0 b)
    go p (Pi n t b)    = paren (p > 0) ("(" ++ show n ++ " : " ++ go 0 t ++ ") -> " ++ go 0 b)
    go p (Let n t v b) = paren (p > 0) ("let " ++ show n ++ " : " ++ go 0 t ++ " := " ++ go 0 v ++ "; " ++ go 0 b)
    go _ (Proj s i b)  = go 2 b ++ "." ++ showName s ++ "#" ++ show i
    go _ (NatLit n)    = show n
    go _ (StrLit s)    = show (B.unpack s)
    commas = foldr1 (\a b -> a ++ ", " ++ b)
    paren True s  = "(" ++ s ++ ")"
    paren False s = s
