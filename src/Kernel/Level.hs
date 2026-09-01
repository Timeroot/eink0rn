-- | Universe levels.
--
-- Semantics: a level denotes a function from assignments of its parameters to
-- naturals.
--
-- > [[0]]        rho = 0
-- > [[succ l]]   rho = [[l]] rho + 1
-- > [[max a b]]  rho = max ([[a]] rho) ([[b]] rho)
-- > [[imax a b]] rho = 0                      if [[b]] rho = 0
-- >                    max ([[a]] rho) ([[b]] rho)  otherwise
-- > [[param p]]  rho = rho p
--
-- @l1 <= l2@ holds when it holds under /every/ assignment; @l1 ~ l2@ is
-- @l1 <= l2 && l2 <= l1@.  Lean has no cumulativity, so the kernel only ever
-- needs @~@ -- but @<=@ is how @~@ is decided.
module Kernel.Level
  ( Level (..)
  , mkSucc, mkMax, mkIMax
  , addOffset
  , normalize
  , levelLeq
  , levelEquiv
  , isDefinitelyZero
  , isDefinitelyNonZero
  , substLevel
  , instLevelParams
  , levelParamsOf
  , levelGround
  , levelHash
  , showLevel
  ) where

import           Data.List     (foldl', sortBy, nub)
import           Data.Ord      (comparing)
import qualified Data.Map.Strict as M
import           Kernel.Name

data Level
  = LZero
  | LSucc  !Level
  | LMax   !Level !Level
  | LIMax  !Level !Level
  | LParam !Name
  deriving (Eq, Ord)

-- | Does this level mention no parameter at all?
--
-- @null . 'levelParamsOf'@ answers the same question and allocates a list and a
-- 'nub' to do it.  This one is asked at every 'Kernel.Expr.Sort' and
-- 'Kernel.Expr.Const' that is built, which is tens of millions of times a run,
-- so it may not allocate.
levelGround :: Level -> Bool
levelGround l = case l of
  LZero     -> True
  LSucc a   -> levelGround a
  LMax  a b -> levelGround a && levelGround b
  LIMax a b -> levelGround a && levelGround b
  LParam _  -> False

-- | A structural hash.  Levels are small, so this is recomputed rather than
-- cached; it exists so that 'Kernel.Expr.Expr' can cache a hash of its own.
levelHash :: Level -> Int
levelHash l = case l of
  LZero     -> 17
  LSucc a   -> hashMix 3 (levelHash a)
  LMax  a b -> hashMix (hashMix 5 (levelHash a)) (levelHash b)
  LIMax a b -> hashMix (hashMix 7 (levelHash a)) (levelHash b)
  LParam n  -> hashMix 11 (nameHash n)

instance Show Level where show = showLevel

showLevel :: Level -> String
showLevel = go (0 :: Int)
  where
    go _ LZero        = "0"
    go _ l@(LSucc _)  = case peel l 0 of
                          (LZero, n) -> show n
                          (b, n)     -> go 1 b ++ "+" ++ show n
    go p (LMax a b)   = paren (p > 0) ("max " ++ go 1 a ++ " " ++ go 1 b)
    go p (LIMax a b)  = paren (p > 0) ("imax " ++ go 1 a ++ " " ++ go 1 b)
    go _ (LParam n)   = showName n
    peel (LSucc x) n  = peel x (n + 1 :: Integer)
    peel x n          = (x, n)
    paren True s  = "(" ++ s ++ ")"
    paren False s = s

-- Smart constructors ----------------------------------------------------------
--
-- These implement the identities that hold for /all/ assignments, so a level
-- built with them denotes exactly what the unsimplified one did.

mkSucc :: Level -> Level
mkSucc = LSucc

addOffset :: Integer -> Level -> Level
addOffset n l
  | n <= 0    = l
  | otherwise = addOffset (n - 1) (LSucc l)

-- | @max@, normalising through the offset/atom representation below.
mkMax :: Level -> Level -> Level
mkMax a b = fromEntries (entries a ++ entries b)

-- | @imax a b@.  Case analysis on @b@ discharges every shape except a bare
-- parameter, so a normalised level only ever contains @LIMax _ (LParam _)@.
mkIMax :: Level -> Level -> Level
mkIMax a b = case b of
  LZero      -> LZero                          -- imax a 0 = 0
  LSucc _    -> mkMax a b                      -- b > 0, so imax a b = max a b
  LMax c d   -> mkMax (mkIMax a c) (mkIMax a d)  -- imax a (max c d) = max (imax a c) (imax a d)
  LIMax c d  -> mkIMax (mkMax a c) d           -- imax a (imax c d) = imax (max a c) d
  LParam _
    | a == b    -> a                           -- imax a a = a
    | a == LZero -> b                          -- imax 0 b = b
    | otherwise -> LIMax a b

-- Offset/atom normal form -----------------------------------------------------
--
-- Every level is equal to a finite @max@ of entries @atom + k@ where an atom is
-- @0@, a parameter, or an irreducible @imax@.  Canonicalising that multiset
-- (dedupe, drop dominated entries, sort) makes many equalities syntactic.

data Atom = AZero | AParam !Name | AIMax !Level !Level
  deriving (Eq, Ord)

entries :: Level -> [(Atom, Integer)]
entries = go 0
  where
    go k LZero       = [(AZero, k)]
    go k (LSucc a)   = go (k + 1) a
    go k (LMax a b)  = go k a ++ go k b
    go k (LParam p)  = [(AParam p, k)]
    go k (LIMax a b) = case mkIMax a b of
      LIMax a' b' -> [(AIMax a' b', k)]
      other       -> go k other

fromEntries :: [(Atom, Integer)] -> Level
fromEntries es0 =
  let best    = M.toList (M.fromListWith max es0)   -- keep the largest offset per atom
      nonZero = [ e | e@(a, _) <- best, a /= AZero ]
      maxNZ   = maximum (0 : map snd nonZero)
      -- @0 + k@ is dominated by @atom + j@ whenever @j >= k@, because atoms are >= 0.
      kept    = case [ k | (AZero, k) <- best ] of
                  (k : _) | null nonZero -> [(AZero, k)]
                          | k <= maxNZ   -> nonZero
                          | otherwise    -> (AZero, k) : nonZero
                  _                      -> nonZero
      sorted  = sortBy (comparing fst) kept
  in case sorted of
       []     -> LZero
       (e:es) -> foldl' (\acc x -> LMax acc (unAtom x)) (unAtom e) es
  where
    unAtom (a, k) = addOffset k $ case a of
      AZero     -> LZero
      AParam p  -> LParam p
      AIMax x y -> LIMax x y

-- | Rebuild a level in canonical form.  Idempotent.
normalize :: Level -> Level
normalize l = case l of
  LZero     -> LZero
  LParam _  -> l
  LSucc a   -> addOffset 1 (normalize a)
  LMax a b  -> mkMax (normalize a) (normalize b)
  LIMax a b -> mkIMax (normalize a) (normalize b)

-- Decision procedure ----------------------------------------------------------

-- | @levelLeq a b@ decides @a <= b@ under all parameter assignments.
levelLeq :: Level -> Level -> Bool
levelLeq a b = leqCore (normalize a) (normalize b) 0

-- | @leqCore a b d@ decides @a <= b + d@ (@d@ may be negative).
--
-- Every rule below is an equivalence except the @max@-on-the-right rule, which
-- is only sufficient; it is applied last, after @imax@ case splitting has
-- removed the shapes that would make it lose information.
leqCore :: Level -> Level -> Integer -> Bool
leqCore a b d
  | a == b, d >= 0                = True
  | LZero <- a, d >= 0            = True
  | LSucc a' <- a                 = leqCore a' b (d - 1)
  | LSucc b' <- b                 = leqCore a b' (d + 1)
  | LMax a1 a2 <- a               = leqCore a1 b d && leqCore a2 b d
  | Just p <- splitParam a        = splitOn p
  | Just p <- splitParam b        = splitOn p
  | LMax b1 b2 <- b               = leqCore a b1 d || leqCore a b2 d
  | LZero <- a                    = d >= 0
  | LZero <- b                    = False       -- a is a parameter: unbounded
  | LParam p <- a, LParam q <- b  = p == q && d >= 0
  | otherwise                     = False
  where
    -- Case split on whether @p@ is zero, which is the only thing an @imax@
    -- looks at.  Both branches strictly reduce the number of irreducible
    -- @imax@ nodes, so this terminates.
    splitOn p =
      let go v = leqCore (normalize (substLevel p v a)) (normalize (substLevel p v b)) d
      in go LZero && go (LSucc (LParam p))

-- | The parameter guarding the first irreducible @imax@, if any.
splitParam :: Level -> Maybe Name
splitParam l = case l of
  LZero              -> Nothing
  LParam _           -> Nothing
  LSucc a            -> splitParam a
  LMax a b           -> splitParam a `orElse` splitParam b
  LIMax _ (LParam p) -> Just p
  LIMax a b          -> splitParam a `orElse` splitParam b
  where orElse (Just x) _ = Just x
        orElse Nothing  y = y

levelEquiv :: Level -> Level -> Bool
levelEquiv a b =
  let a' = normalize a
      b' = normalize b
  in a' == b' || (leqCore a' b' 0 && leqCore b' a' 0)

-- | Is this level zero under every assignment?  (i.e. is @Sort l@ a @Prop@)
isDefinitelyZero :: Level -> Bool
isDefinitelyZero l = levelLeq l LZero

-- | Is this level nonzero under every assignment?  (i.e. is @Sort l@ never a @Prop@)
isDefinitelyNonZero :: Level -> Bool
isDefinitelyNonZero l = levelLeq (LSucc LZero) l

-- Substitution ----------------------------------------------------------------

substLevel :: Name -> Level -> Level -> Level
substLevel p v = go
  where
    go LZero        = LZero
    go (LSucc a)    = LSucc (go a)
    go (LMax a b)   = LMax (go a) (go b)
    go (LIMax a b)  = LIMax (go a) (go b)
    go l@(LParam q) | q == p    = v
                    | otherwise = l

-- | Simultaneous substitution of a declaration's level parameters.
--
-- The two lists are walked side by side rather than packed into a map first.
-- A declaration has a handful of universe parameters -- most have none and
-- almost all the rest have one -- so the map was a tree of one node, built
-- afresh at every call, and looked up with a 'compare' that has to walk two
-- whole names to report that they are equal.  @(==)@ on a 'Name' answers that
-- one from the pointers.
--
-- The first occurrence of a parameter wins, where the map kept the last.  No
-- declaration binds one twice -- 'Front.Block.checkLevelParams' is a premise of
-- every rule that admits one -- so nothing this is ever called on can tell.
instLevelParams :: [Name] -> [Level] -> Level -> Level
instLevelParams ps vs = go
  where
    go LZero        = LZero
    go (LSucc a)    = LSucc (go a)
    go (LMax a b)   = LMax (go a) (go b)
    go (LIMax a b)  = LIMax (go a) (go b)
    go l@(LParam q) = look ps vs
      where
        look (p : ps') (v : vs') | p == q    = v
                                 | otherwise = look ps' vs'
        look _         _                     = l

levelParamsOf :: Level -> [Name]
levelParamsOf = nub . go
  where
    go LZero       = []
    go (LSucc a)   = go a
    go (LMax a b)  = go a ++ go b
    go (LIMax a b) = go a ++ go b
    go (LParam p)  = [p]
