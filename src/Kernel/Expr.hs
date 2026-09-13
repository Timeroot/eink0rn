{-# LANGUAGE BangPatterns     #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE MagicHash        #-}
{-# LANGUAGE PatternSynonyms  #-}
{-# LANGUAGE ScopedTypeVariables #-}
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
--   constant time and gives 'Kernel.Check' something to key a memo table on;
--
-- * and the same nodes cache whether they contain an 'FVar', which is how
--   'Kernel.Check' tells a subterm of the declaration being checked from one of
--   the context it is being checked in.
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
  , instNPrefix
  , inst1
  -- * Local constants
  , abstractFVars
  , instantiateBody
  -- * Queries
  , hasLooseBVars
  , hasFVars
  , looseBVarRange
  , occursConst
  , constsMeeting
  , instLevelsE
  , showExpr
  ) where

import           Control.Monad.ST      (ST, runST)
import           Data.Array.Base       (unsafeRead, unsafeWrite)
import           Data.Array.ST         (STArray, STUArray, newArray)
import           Data.Bits             (complement, shiftL, shiftR, (.&.),
                                        (.|.))
import qualified Data.ByteString.Char8 as B
import           Data.IntMap.Strict    (IntMap)
import qualified Data.IntMap.Strict    as IM
import           Data.STRef            (STRef, modifySTRef', newSTRef, readSTRef,
                                        writeSTRef)
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

-- | The real representation.  @X@-prefixed constructors are private.
--
-- The leading @Int@ is the node's cached hash, except on the five constructors
-- that can contain a bound variable, where it is a hash and a
-- 'looseBVarRange' packed into the one word: the range in the low
-- 'rangeBits', the hash above it, and 'hasFVars' in the top bit.  All three
-- caches are wanted on every one of those
-- nodes and neither needs a full word, and an @Expr@ is what a run of this
-- kernel is almost entirely made of -- @XApp@ alone is 38% of the live heap at
-- @std@'s peak and 70% of it at @mathlib@'s -- so the word saved is worth the
-- shift.  See 'mkHR'.
data Expr
  = XBVar !Int                                  -- ^ de Bruijn index
  | XFVar !Int                                  -- ^ local constant (checker-internal)
  | XSort !Int !Level
  | XConst !Int !Name ![Level]
  | XApp !Int !Expr !Expr
  | XLam !Int !Binder !Expr !Expr               -- ^ @fun (x : t) => b@
  | XPi  !Int !Binder !Expr !Expr               -- ^ @(x : t) -> b@
  | XLet !Int !Binder !Expr !Expr !Expr         -- ^ @let x : t := v; b@
  | XProj !Int !Name !Int !Expr                 -- ^ @s.i@ at structure type @T@ (0-based)
  | XNatLit !Int !Integer                       -- ^ abbreviation for a @Nat.succ@ tower
  | XStrLit !Int !B.ByteString                  -- ^ abbreviation for @String.mk [...]@

-- | How many low bits of a packed word hold the range.
--
-- Sixteen million binders deep is not a term any exporter emits, and the
-- remaining forty bits are more hash than the caches can use: they are only
-- ever a filter in front of a structural test and an index into a table, so a
-- collision costs a comparison and never an answer.  The width is nonetheless
-- not load-bearing -- 'looseBVarRange' is exact at every width, because a range
-- too large to store is stored as 'satRange' and recomputed on demand.
rangeBits :: Int
rangeBits = 24

rangeMask :: Int
rangeMask = (1 `shiftL` rangeBits) - 1

-- | The stored range meaning \"at least this, and the exact figure was not
-- representable\".  Reaching it costs a traversal and nothing else.
satRange :: Int
satRange = rangeMask

-- | Pack a hash and a range into one word.
--
-- The /top/ bits of the hash are the ones kept.  'hashMix' ends in a multiply,
-- which mixes upwards -- bit @i@ of a product depends only on bits @<= i@ of
-- its arguments -- so the low bits of a hash are the least mixed, and they are
-- exactly the bits every table here indexes on.  Shifting them out and handing
-- back bits 24 and up is therefore not merely lossless where it matters, it is
-- an improvement on what the tables saw before.
mkHR :: Int -> Int -> Int
mkHR h r = (h .&. complement rangeMask) .|. (if r < satRange then r else satRange)
{-# INLINE mkHR #-}

-- | The bit of a packed word that says the node contains an 'FVar'.
--
-- The sign bit, so that the query is a comparison against zero.  It costs the
-- hash its top bit, which is one bit of a filter in front of a structural test.
fvarBit :: Int
fvarBit = minBound

-- | 'mkHR', with 'fvarBit' set as the node's children dictate.
mkHRF :: Bool -> Int -> Int -> Int
mkHRF v h r | v         = mkHR h r .|. fvarBit
            | otherwise = mkHR h r .&. complement fvarBit
{-# INLINE mkHRF #-}

-- | Does an 'FVar' occur in the term?  Constant time.
--
-- Exact, and unlike 'looseBVarRange' it never saturates: one bit is all the
-- question needs, and the pattern synonyms below or it up from the children.
hasFVars :: Expr -> Bool
hasFVars e = case e of
  XFVar _         -> True
  XApp hr _ _     -> hr < 0
  XLam hr _ _ _   -> hr < 0
  XPi  hr _ _ _   -> hr < 0
  XLet hr _ _ _ _ -> hr < 0
  XProj hr _ _ _  -> hr < 0
  _               -> False

-- | The range a packed node stores, saturation and all.  Used where the answer
-- is about to be packed again, so that a saturated child keeps its parent
-- saturated instead of being expanded and re-clamped.
rawRange :: Expr -> Int
rawRange e = case e of
  XBVar i        -> i + 1
  XApp hr _ _    -> hr .&. rangeMask
  XLam hr _ _ _  -> hr .&. rangeMask
  XPi  hr _ _ _  -> hr .&. rangeMask
  XLet hr _ _ _ _ -> hr .&. rangeMask
  XProj hr _ _ _ -> hr .&. rangeMask
  _              -> 0

-- | 'rawRange' of a binder's body, seen from outside the binder, and still
-- saturated if it was.  Decrementing 'satRange' would turn \"at least sixteen
-- million\" into an exact figure that is wrong.
rawUnder :: Expr -> Int
rawUnder b = let r = rawRange b
             in if r == satRange then satRange else max 0 (r - 1)

-- | Smallest @k@ such that no @BVar i@ with @i >= k@ occurs free.  Constant
-- time: it is either immediate or cached.
--
-- Exact, including on the node whose cached range saturated: that one is
-- recomputed from its children, which is a traversal no export has ever
-- provoked and which is here so that the width of the field cannot be an
-- assumption about the file.
looseBVarRange :: Expr -> Int
looseBVarRange e = let r = rawRange e
                   in if r == satRange then exactRange e else r

-- | The range of a node whose cached one saturated.  Memoised, so it is linear
-- in the graph rather than in its unfolding; a child whose own range fits is
-- read straight off it.
exactRange :: Expr -> Int
exactRange e0 = runST (newMemo >>= \ref -> go ref e0)
  where
    go ref ex
      | r /= satRange = pure r
      | otherwise = memoAt ref 0 ex $ case ex of
          XApp _ f a      -> max <$> go ref f <*> go ref a
          XLam _ _ t b    -> binder ref t b
          XPi  _ _ t b    -> binder ref t b
          XLet _ _ t v b  -> do t' <- go ref t; v' <- go ref v; b' <- go ref b
                                pure (max t' (max v' (max 0 (b' - 1))))
          XProj _ _ _ b   -> go ref b
          -- An @XBVar@ whose index happens to land on 'satRange' exactly: the
          -- stored figure is the true one, and there is nothing under it.
          _               -> pure r
      where r = rawRange ex
    binder ref t b = do t' <- go ref t; b' <- go ref b
                        pure (max t' (max 0 (b' - 1)))
{-# NOINLINE exactRange #-}

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
  XApp hr _ _      -> hr `shiftR` rangeBits
  XLam hr _ _ _    -> hr `shiftR` rangeBits
  XPi  hr _ _ _    -> hr `shiftR` rangeBits
  XLet hr _ _ _ _  -> hr `shiftR` rangeBits
  XProj hr _ _ _   -> hr `shiftR` rangeBits
  XNatLit h _      -> h
  XStrLit h _      -> h

-- | Structural equality, with the two caches doing the work.
--
-- The pointer test is what makes comparing shared subterms affordable: an
-- exported term is a graph, and its tree unfolding can be exponentially larger.
-- The hash test then settles almost every remaining pair at the root.
instance Eq Expr where
  a == b = ptrEq a b || (exprHash a == exprHash b && eqE a b)

-- | An answer, and what is left of the visit budget that produced it.
--
-- Every budgeted walk in this module hands back one of these, and none of them
-- allocates one: a strict constructor with an unpacked field is a shape GHC
-- returns in registers.  Saying the same thing with an @(a, Int)@ pair costs
-- three heap objects at every node visited -- the pair, a box for the @Int@
-- inside it, and a thunk for the lazy @let@ that takes it apart again -- and
-- these walks run over every term the checker touches.
data Step a = Step !a {-# UNPACK #-} !Int

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
    Step r k | k >= 0 -> r
    _                 -> runST (newSTRef IM.empty >>= \ref -> go ref a0 b0)
  where
    plain :: Int -> Expr -> Expr -> Step Bool
    plain !k x y
      | k < 0                    = Step False k
      | ptrEq x y                = Step True k
      | exprHash x /= exprHash y = Step False k
      | otherwise = case (x, y) of
          (XApp _ f a, XApp _ g b) -> two (k - 1) f g a b
          (XLam _ n t b, XLam _ n' t' b')
            | n == n'   -> two (k - 1) t t' b b'
          (XPi _ n t b, XPi _ n' t' b')
            | n == n'   -> two (k - 1) t t' b b'
          (XLet _ n t v b, XLet _ n' t' v' b')
            | n == n'   -> case two (k - 1) t t' v v' of
                Step True k1 -> plain k1 b b'
                r            -> r
          (XProj _ s i b, XProj _ s' i' b')
            | i == i', s == s' -> plain (k - 1) b b'
          _ -> Step (eqLeaf x y) (k - 1)

    two !k f g a b = case plain k f g of
      Step True k1 -> plain k1 a b
      r            -> r

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
      (XApp _ f a, XApp _ g b) -> andM (go ref f g) (go ref a b)
      (XLam _ n t b, XLam _ n' t' b')
        | n == n' -> andM (go ref t t') (go ref b b')
      (XPi _ n t b, XPi _ n' t' b')
        | n == n' -> andM (go ref t t') (go ref b b')
      (XLet _ n t v b, XLet _ n' t' v' b')
        | n == n' -> andM (go ref t t') (andM (go ref v v') (go ref b b'))
      (XProj _ s i b, XProj _ s' i' b')
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
-- Much larger than 'instBudget', because the two budgets buy different things.
-- Overrunning 'instBudget' throws away a rebuilt term; overrunning this one
-- throws away a walk that allocated nothing at all, so the only cost of setting
-- it high is the comparisons themselves, and the table it defers is a
-- 'Data.IntMap.IntMap' of association lists -- the most expensive memo in the
-- checker per entry.
--
-- Measured on @std@, bytes allocated: 1024 comparisons cost 141.6 GB, 4096
-- 136.5, 16384 134.1, 65536 132.7, and past that it flattens -- 262144 costs
-- 132.5 and 1048576 costs 132.4, by which point the wasted walks are showing up
-- in the clock.  What still protects the pathological case is that the bound
-- holds: a comparison of two @brecOn@ unfoldings gives up after 65536 pairs and
-- starts again with the table.
--
-- Confirmed against the worst declaration in @mathlib@ -- the @Scheme@ theorem
-- the README names, which is where a bad choice here would hurt most.  Checked
-- on its own at @-j2 +RTS -A128m@: 4096 takes 347.5s and allocates 224.5 GB,
-- 65536 takes 351.5s and 223.1 GB, 1048576 takes 499.6s and 226.6 GB.  So the
-- flat middle of the @std@ curve is flat here too, and the walks the budget
-- pays for on that theorem are genuine comparisons rather than waste: dividing
-- the budget by sixteen buys about one per cent, and multiplying it by sixteen
-- costs forty.  The structural fix would be hash-consing 'Expr', not a number
-- here.
eqBudget :: Int
eqBudget = 65536

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
    fields (XApp _ f x)     (XApp _ g y)     = compare f g <> compare x y
    fields (XLam _ n t x)   (XLam _ m u y)   =
      compare n m <> compare t u <> compare x y
    fields (XPi _ n t x)    (XPi _ m u y)    =
      compare n m <> compare t u <> compare x y
    fields (XLet _ n t v x) (XLet _ m u w y) =
      compare n m <> compare t u <> compare v w <> compare x y
    fields (XProj _ s i x)  (XProj _ r j y)  =
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
hasLooseBVars e = rawRange e > 0

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
pattern App f a <- XApp _ f a
  where App f a = XApp (mkHRF (hasFVars f || hasFVars a)
                              (h2 31 (exprHash f) (exprHash a))
                              (max (rawRange f) (rawRange a))) f a

pattern Lam :: Binder -> Expr -> Expr -> Expr
pattern Lam n t b <- XLam _ n t b
  where Lam n t b = XLam (mkHRF (hasFVars t || hasFVars b)
                                (h2 37 (exprHash t) (exprHash b))
                                (max (rawRange t) (rawUnder b))) n t b

pattern Pi :: Binder -> Expr -> Expr -> Expr
pattern Pi n t b <- XPi _ n t b
  where Pi n t b = XPi (mkHRF (hasFVars t || hasFVars b)
                              (h2 41 (exprHash t) (exprHash b))
                              (max (rawRange t) (rawUnder b))) n t b

pattern Let :: Binder -> Expr -> Expr -> Expr -> Expr
pattern Let n t v b <- XLet _ n t v b
  where Let n t v b =
          XLet (mkHRF (hasFVars t || hasFVars v || hasFVars b)
                      (h3 43 (exprHash t) (exprHash v) (exprHash b))
                      (max (rawRange t) (max (rawRange v) (rawUnder b)))) n t v b

pattern Proj :: Name -> Int -> Expr -> Expr
pattern Proj s i b <- XProj _ s i b
  where Proj s i b = XProj (mkHRF (hasFVars b)
                                  (h3 47 (nameHash s) i (exprHash b))
                                  (rawRange b)) s i b

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
-- them costs an insertion.  Chaining would make a lookup complete -- it would
-- find an entry whenever one exists -- but a memo does not have to be complete
-- to be correct, only to be right when it answers.  Since a miss costs a
-- recomputation and a hash collision between two nodes reached in the same
-- traversal is rare, one slot per hash is the better trade, and it is the
-- allocation of the chain that it saves.
--
-- An array rather than a 'Data.IntMap.IntMap', for the same reason
-- "Kernel.Cache" is one: with a slot per hash, the map's insertion copies the
-- path it came down -- some forty words, all of them garbage a moment later --
-- where the array writes one.  Both answer the same questions; only the litter
-- differs, and these tables are where a run leaves most of it.  The table
-- doubles when it has taken as many entries as it has slots, which is what keeps
-- eviction rare on a traversal large enough for eviction to matter.
data Slot a = Vacant | Slot !Expr !Int a

-- | The mask and the entry count, then the slots.  The slot count is a power of
-- two, so the mask is one less than it and indexing is a bitwise and.
--
-- The two numbers live in a pair of machine words rather than in a record
-- beside the array, because an insertion changes nothing else: holding them in
-- a boxed 'Rep' meant building a fresh one for every entry, which came to more
-- litter than the entries themselves.  The array still needs a cell of its own,
-- since growing the table replaces it.
data Memo s a = Memo !(STUArray s Int Int) !(STRef s (STArray s Int (Slot a)))

-- | Small: a table is only built for a traversal that ran past its budget, and
-- most of those are not much past it.
memoSlots :: Int
memoSlots = 64

newMemo :: ST s (Memo s a)
newMemo = do
  hdr <- newArray (0, 1) 0
  unsafeWrite hdr 0 (memoSlots - 1)
  arr <- newArray (0, memoSlots - 1) Vacant
  Memo hdr <$> newSTRef arr

-- | Inlined, which is the point of it being this small: the action it is given
-- is written at the call site and would otherwise be built there as a closure,
-- once per node of every traversal that runs past its budget.
memoAt :: Memo s a -> Int -> Expr -> ST s a -> ST s a
memoAt m@(Memo hdr ref) d ex mk = do
  mask <- unsafeRead hdr 0
  arr  <- readSTRef ref
  let key = hashMix (exprHash ex) d
  s <- unsafeRead arr (key .&. mask)
  case s of
    Slot k d' r | d == d', ptrEq k ex -> pure r
    _ -> do
      -- @mk@ recurs, and so may have grown the table under us: read it again.
      r     <- mk
      mask' <- unsafeRead hdr 0
      n     <- unsafeRead hdr 1
      arr'  <- readSTRef ref
      unsafeWrite arr' (key .&. mask') (Slot ex d r)
      let n' = n + 1
      if n' > mask' then growMemo m mask' arr'
                    else unsafeWrite hdr 1 n'
      pure r
{-# INLINE memoAt #-}

-- | Double the table and rehang what survived.  An entry carries everything its
-- key is made of, so nothing has to be remembered alongside it.
growMemo :: forall s a. Memo s a -> Int -> STArray s Int (Slot a) -> ST s ()
growMemo (Memo hdr ref) mask arr = do
  let mask' = mask * 2 + 1
  arr' <- newArray (0, mask') Vacant :: ST s (STArray s Int (Slot a))
  let go :: Int -> Int -> ST s Int
      go !i !n
        | i > mask  = pure n
        | otherwise = unsafeRead arr i >>= \case
            Vacant         -> go (i + 1) n
            s@(Slot k d _) -> do
              unsafeWrite arr' (hashMix (exprHash k) d .&. mask') s
              go (i + 1) (n + 1)
  n <- go 0 0
  unsafeWrite hdr 0 mask'
  unsafeWrite hdr 1 n
  writeSTRef ref arr'
{-# NOINLINE growMemo #-}

-- | How many nodes a level substitution may visit before it is worth a memo
-- table.
levelBudget :: Int
levelBudget = 512

-- | How many nodes a substitution may visit before it is worth a memo table.
--
-- The tradeoff is not the obvious one.  A budget that is too small does not
-- merely fail to catch a little sharing: the unmemoised walk that overruns it
-- throws away everything it has rebuilt and the memoised walk starts the term
-- again from the top, so the price of guessing low is paid twice over.  Against
-- that, the budget bounds the waste at one visit per node and the walk it
-- protects against is the one that allocates a table for a term with no sharing
-- in it at all.
--
-- Measured on @std@: 64 visits cost 150.1 GB of allocation, 128 cost 145.9,
-- 256 cost 142.8, 512 cost 141.6, 1024 the same again, and 2048 cost 144.9 as
-- the discarded rebuilds started to outweigh the tables they saved.
instBudget :: Int
instBudget = 512

-- de Bruijn plumbing ----------------------------------------------------------

-- | @liftE d k e@ adds @k@ to every bound variable of @e@ with index @>= d@.
--
-- A subterm whose loose variables all sit below @d@ is returned as is, sharing
-- rather than copying.  This is what keeps substitution proportional to the
-- part of the term that actually mentions the variable.
--
-- Budgeted then memoised, as 'instN' is and for the same reason: almost every
-- call shifts a handful of nodes, and setting up a table for that costs more
-- than the walk.
liftE :: Int -> Int -> Expr -> Expr
liftE _ 0 e = e
liftE d0 k e0
  | looseBVarRange e0 <= d0 = e0
  | Step r q <- plain instBudget d0 e0, q >= 0 = r
  | otherwise = runST (newMemo >>= \ref -> go ref d0 e0)
  where
    plain !q !d' ex
      | q < 0                    = Step ex q
      | looseBVarRange ex <= d'  = Step ex q
      | otherwise = case ex of
          BVar i        -> Step (BVar (i + k)) q'
          App f a       -> case plain q' d' f of { Step f' q1 ->
                           case plain q1 d' a of { Step a' q2 ->
                           Step (App f' a') q2 }}
          Lam n t b     -> case plain q' d' t of { Step t' q1 ->
                           case plain q1 (d' + 1) b of { Step b' q2 ->
                           Step (Lam n t' b') q2 }}
          Pi  n t b     -> case plain q' d' t of { Step t' q1 ->
                           case plain q1 (d' + 1) b of { Step b' q2 ->
                           Step (Pi n t' b') q2 }}
          Let n t v b   -> case plain q' d' t of { Step t' q1 ->
                           case plain q1 d' v of { Step v' q2 ->
                           case plain q2 (d' + 1) b of { Step b' q3 ->
                           Step (Let n t' v' b') q3 }}}
          Proj s i b    -> case plain q' d' b of { Step b' q1 ->
                           Step (Proj s i b') q1 }
          _             -> Step ex q'   -- unreachable: range would be 0
      where q' = q - 1

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
instN vs e
  | looseBVarRange e == 0 = e
  | otherwise             = instNPrefix (length vs) vs e

-- | 'instN' against the first @n@ of @vs@, for a caller that already knows @n@.
--
-- @instNPrefix n vs@ is @instN (take n vs)@ whenever @vs@ has at least @n@
-- entries.  The point is the ones it does not have to build: 'Kernel.Check' hands
-- over its whole local environment and a term that mentions the innermost few
-- of it, eleven million times over a run of @std@, and a @take@ at each of those
-- allocates a list only to walk it once and drop it.
instNPrefix :: Int -> [Expr] -> Expr -> Expr
instNPrefix _ _ e0
  | looseBVarRange e0 == 0 = e0
instNPrefix n vs e0
  | Step r k <- plain instBudget 0 e0, k >= 0 = r
  | otherwise = runST (newMemo >>= \ref -> go ref 0 e0)
  where
    -- Returns the rewritten node and what is left of the budget; a negative
    -- budget means the answer is unfinished and must be thrown away.
    plain !k !d ex
      | k < 0                  = Step ex k
      | looseBVarRange ex <= d = Step ex k
      | otherwise = case ex of
          BVar i
            | i < d + n   -> Step (liftE 0 d (vs !! (i - d))) k'
            | otherwise   -> Step (BVar (i - n)) k'
          App f a       -> case plain k' d f of { Step f' k1 ->
                           case plain k1 d a of { Step a' k2 ->
                           Step (App f' a') k2 }}
          Lam nm t b    -> case plain k' d t of { Step t' k1 ->
                           case plain k1 (d + 1) b of { Step b' k2 ->
                           Step (Lam nm t' b') k2 }}
          Pi  nm t b    -> case plain k' d t of { Step t' k1 ->
                           case plain k1 (d + 1) b of { Step b' k2 ->
                           Step (Pi nm t' b') k2 }}
          Let nm t v b  -> case plain k' d t of { Step t' k1 ->
                           case plain k1 d v of { Step v' k2 ->
                           case plain k2 (d + 1) b of { Step b' k3 ->
                           Step (Let nm t' v' b') k3 }}}
          Proj s i b    -> case plain k' d b of { Step b' k1 ->
                           Step (Proj s i b') k1 }
          _             -> Step ex k'
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
-- Budgeted then memoised, as 'instN' is.  Closing a binder body over the one
-- local that binder introduced is the single most frequent traversal the checker
-- performs -- 'Kernel.Check.inferCore' does it for every @Lam@ it reads -- and
-- most of those bodies are small.
--
-- Unlike 'liftE' there is no cheap test for \"this subterm cannot be affected\":
-- an 'FVar' is not counted by 'looseBVarRange'.  So the saving is in the
-- rebuilding rather than in the walk, and both paths hand back the original node
-- whenever its children come back unchanged, which for a term that mentions the
-- local in one place leaves the rest of it shared.
abstractFVars :: [Int] -> Expr -> Expr
abstractFVars [] e = e
abstractFVars ids e0
  | Step r q <- plain instBudget 0 e0, q >= 0 = r
  | otherwise = runST (newMemo >>= \ref -> go ref 0 e0)
  where
    n = length ids
    -- One local is the common case by a wide margin; the general table is built
    -- once rather than at every occurrence.
    pos = case ids of
      [x] -> \i -> if i == x then Just 0 else Nothing
      _   -> let table = zip ids [0 ..] in \i -> lookup i table

    plain !q !d ex
      | q < 0     = Step ex q
      | otherwise = case ex of
          FVar i        -> case pos i of
                             Just k  -> Step (BVar (d + n - 1 - k)) q'
                             Nothing -> Step ex q'
          App f a       -> case plain q' d f of { Step f' q1 ->
                           case plain q1 d a of { Step a' q2 ->
                           Step (keep2 ex f f' a a' (App f' a')) q2 }}
          Lam nm t b    -> case plain q' d t of { Step t' q1 ->
                           case plain q1 (d + 1) b of { Step b' q2 ->
                           Step (keep2 ex t t' b b' (Lam nm t' b')) q2 }}
          Pi  nm t b    -> case plain q' d t of { Step t' q1 ->
                           case plain q1 (d + 1) b of { Step b' q2 ->
                           Step (keep2 ex t t' b b' (Pi nm t' b')) q2 }}
          Let nm t v b  -> case plain q' d t of { Step t' q1 ->
                           case plain q1 d v of { Step v' q2 ->
                           case plain q2 (d + 1) b of { Step b' q3 ->
                           Step (if ptrEq t t' && ptrEq v v' && ptrEq b b'
                                   then ex else Let nm t' v' b') q3 }}}
          Proj s i b    -> case plain q' d b of { Step b' q1 ->
                           Step (if ptrEq b b' then ex else Proj s i b') q1 }
          _             -> Step ex q'
      where q' = q - 1

    keep2 ex x x' y y' new = if ptrEq x x' && ptrEq y y' then ex else new

    go ref d ex = case ex of
      FVar i | Just k <- pos i -> pure (BVar (d + n - 1 - k))
             | otherwise       -> pure ex
      BVar _        -> pure ex
      Sort _        -> pure ex
      Const _ _     -> pure ex
      NatLit _      -> pure ex
      StrLit _      -> pure ex
      _             -> memoAt ref d ex $ case ex of
        App f a       -> do f' <- go ref d f; a' <- go ref d a
                            pure (keep2 ex f f' a a' (App f' a'))
        Lam nm t b    -> do t' <- go ref d t; b' <- go ref (d + 1) b
                            pure (keep2 ex t t' b b' (Lam nm t' b'))
        Pi  nm t b    -> do t' <- go ref d t; b' <- go ref (d + 1) b
                            pure (keep2 ex t t' b b' (Pi nm t' b'))
        Let nm t v b  -> do t' <- go ref d t; v' <- go ref d v
                            b' <- go ref (d + 1) b
                            pure (if ptrEq t t' && ptrEq v v' && ptrEq b b'
                                    then ex else Let nm t' v' b')
        Proj s i b    -> do b' <- go ref d b
                            pure (if ptrEq b b' then ex else Proj s i b')

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

-- | Which of these constants a term names.
--
-- @Proj@ carries the structure's name as well as its subterm, and that name is
-- looked for too: it is a reference to a declaration exactly as a 'Const' node
-- is, and a caller asking \"does this term depend on any of these?\" means it
-- to count.
--
-- The filtering is not a refinement of collecting every constant and
-- intersecting afterwards -- it is the difference between a walk that builds
-- nothing and one that does not.  The one caller ("Front.Lower.barrier") is
-- asking whether a declaration mentions an unsafe constant, and almost none
-- do, so almost every answer here is the empty set and unioning two of those
-- costs nothing.  Building the whole set first and intersecting at the end was
-- three per cent of a run over @std@, essentially all of it in @union@.
constsMeeting :: S.Set Name -> Expr -> S.Set Name
constsMeeting want e0
  | S.null want = S.empty
  | otherwise   = runST (newMemo >>= \ref -> go ref e0)
  where
    keep m | S.member m want = S.singleton m
           | otherwise       = S.empty
    go ref ex = case ex of
      Const m _   -> pure (keep m)
      App f a     -> memoAt ref 0 ex (both ref f a)
      Lam _ t b   -> memoAt ref 0 ex (both ref t b)
      Pi  _ t b   -> memoAt ref 0 ex (both ref t b)
      Let _ t v b -> memoAt ref 0 ex (S.union <$> both ref t v <*> go ref b)
      Proj s _ b  -> memoAt ref 0 ex (S.union (keep s) <$> go ref b)
      _           -> pure S.empty
    both ref a b = S.union <$> go ref a <*> go ref b

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
  | Step r k <- plain levelBudget e0, k >= 0 = r
  | otherwise = runST (newMemo >>= \ref -> go ref e0)
  where
    sub = instLevelParams ps vs

    -- As in 'instN': the plain recursion first, under a budget, because almost
    -- every body this is asked about is a declared type of a few dozen nodes
    -- and building a memo table for it costs more than the walk.  A negative
    -- budget means the answer is unfinished and is thrown away.
    plain !k ex
      | k < 0     = Step ex k
      | otherwise = case ex of
          Sort l        -> Step (let l' = sub l in if l' == l then ex else Sort l') k'
          Const _ []    -> Step ex k'
          Const n ls    -> Step (let ls' = map sub ls
                                 in if ls' == ls then ex else Const n ls') k'
          App f a       -> case plain k' f of { Step f' k1 ->
                           case plain k1 a of { Step a' k2 ->
                           Step (if ptrEq f f' && ptrEq a a' then ex else App f' a') k2 }}
          Lam n t b     -> case plain k' t of { Step t' k1 ->
                           case plain k1 b of { Step b' k2 ->
                           Step (if ptrEq t t' && ptrEq b b' then ex else Lam n t' b') k2 }}
          Pi  n t b     -> case plain k' t of { Step t' k1 ->
                           case plain k1 b of { Step b' k2 ->
                           Step (if ptrEq t t' && ptrEq b b' then ex else Pi n t' b') k2 }}
          Let n t v b   -> case plain k' t of { Step t' k1 ->
                           case plain k1 v of { Step v' k2 ->
                           case plain k2 b of { Step b' k3 ->
                           Step (if ptrEq t t' && ptrEq v v' && ptrEq b b'
                                   then ex else Let n t' v' b') k3 }}}
          Proj s i b    -> case plain k' b of { Step b' k1 ->
                           Step (if ptrEq b b' then ex else Proj s i b') k1 }
          _             -> Step ex k'
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
