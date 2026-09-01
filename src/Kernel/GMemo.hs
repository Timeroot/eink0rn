{-# LANGUAGE BangPatterns #-}
-- | The one memo table that outlives a declaration: what a /ground/ term
-- reduces to.
--
-- Everything in "Kernel.Cache" is born and dies with a checking episode -- one
-- 'Kernel.Check.runTC', which is roughly half a declaration.  Measured on
-- @init@ and @std@, that is where nearly all of the reduction work goes: 83-86%
-- of the misses the whnf memo takes are on a term some earlier episode already
-- reduced, and the episode boundary is the only place entries are ever lost
-- (bucket eviction and 'Kernel.Check.swapEnv' between them cost 34 and 80
-- recomputations across whole files).  This table is what those misses are
-- offered instead.
--
-- == Why an entry may be kept
--
-- Three things could make a remembered reduct wrong somewhere else, and each is
-- excluded rather than argued away:
--
-- [The environment] A constant that unfolds one way here could unfold another
-- way there.  It cannot: 'Kernel.Env.addConst' is write-once, a term is only
-- well-formed in an environment that already declares every constant it
-- mentions, and reduction introduces only constants from definitions already
-- there.  So a reduct computed in @E@ is the reduct in every @E' ⊇ E@, and the
-- main chain is such a tower.  The environments that are /not/ on it -- the
-- flattening's scratch envs in "Front.Block", where the block's members unfold
-- to the single container and the constructors are the container's, and the
-- same in "Front.Hetero" -- are excluded by the caller instead: see
-- 'Kernel.Check.runTCMain', which is the only thing that turns this table on,
-- and 'Kernel.Check.withEnv', which turns it off again.
--
-- [Local constants] @'Kernel.Expr.FVar' 3@ is a different local in every
-- episode, because the supply restarts with the state.  Excluded by 'groundE'.
--
-- [Universe parameters] @u@ is a different parameter in every declaration, and
-- reduction can reach inference -- the iota rule infers the major premise's
-- type -- which is where an undeclared one is caught.  Excluded by 'groundE'
-- too, which is why it is about levels as well as locals.  It costs almost
-- nothing to ask for both: of 4,259,606 reusable hits on @init@, requiring
-- ground levels as well as no locals gave up 1,863 of them.
--
-- == Why the races are benign
--
-- Under @-jN@ the obligation threads share this table. It is never resized and
-- never rehashed -- that is what 'slots' being a constant buys, and it is the
-- only operation that could show a reader a bucket that is not a bucket.  What
-- remains is that two threads may write the same slot and one entry be lost,
-- and that a reader may see either the old chain or the new one.  Both are
-- fine: a slot always holds a pointer to a fully built, immutable chain, a
-- pointer-sized store does not tear, and a missing entry costs a recomputation
-- and nothing else.  Nothing here can hand back a /wrong/ reduct, which is the
-- only failure that would matter.
module Kernel.GMemo
  ( gmemoLookup
  , gmemoInsert
  ) where

import           Data.Array.Base  (unsafeRead, unsafeWrite)
import           Data.Array.IO    (IOArray, newArray)
import           Data.Bits        (shiftL, (.&.))
import           Kernel.Expr
import           System.IO.Unsafe (unsafePerformIO)

-- | How many slots.  A power of two, so indexing is a bitwise and.
--
-- Fixed, and that is the point: the table is the one thing in the checker whose
-- memory is not returned at the end of a declaration, so it is bounded by
-- construction rather than by hoping the file is small.  With 'slotCap' it
-- admits at most @slots * slotCap@ entries.
--
-- Sized against what the corpora ask for: @init@ reduces 362,029 distinct
-- ground terms in its whole length and @std@ 453,705, and the count grows far
-- slower than the file does -- @std@ has 1.7x @init@'s declarations and 1.25x
-- its ground terms, because what recurs is the same instances and type formers
-- over and over.  At 2^19 slots and four deep the ceiling is two million, which
-- leaves both of those room and still cannot run away on @mathlib@.
slots :: Int
slots = 1 `shiftL` 19

mask :: Int
mask = slots - 1

-- | How many entries one slot may hold before the oldest is dropped.
slotCap :: Int
slotCap = 4

-- | An entry is a link, for the reason 'Kernel.Cache.Chain' gives: the fields
-- in the chain rather than a list of pairs hung off it.
--
-- The fields are lazy, matching 'Kernel.Check.MemoB', whose Haddock explains at
-- length why strictness on a memo's fields is the most expensive thing you can
-- write here.
data GB = GNil | GCons Expr Expr GB

{-# NOINLINE table #-}
table :: IOArray Int GB
table = unsafePerformIO (newArray (0, slots - 1) GNil)

-- | What this term reduces to, if some episode has already found out.
--
-- The caller must have established 'groundE' of the key; this does not re-ask,
-- because the caller is about to need the answer for the insert as well.
gmemoLookup :: Expr -> IO (Maybe Expr)
gmemoLookup e = go <$> unsafeRead table (exprHash e .&. mask)
  where
    go (GCons k v rest) | k == e    = Just v
                        | otherwise = go rest
    go GNil                         = Nothing

-- | Remember it.  Both the key and the value must be 'groundE'.
gmemoInsert :: Expr -> Expr -> IO ()
gmemoInsert k v = do
  let i = exprHash k .&. mask
  old <- unsafeRead table i
  unsafeWrite table i (GCons k v (capG (slotCap - 1) old))

-- | At most @n@ more entries.  Hands back the chain it was given when that is
-- already so, which is the common case and the one worth not copying.
capG :: Int -> GB -> GB
capG n b0 = if fits n b0 then b0 else trunc n b0
  where
    fits !j b = case b of
      GNil         -> True
      GCons _ _ tl -> j > 0 && fits (j - 1 :: Int) tl
    trunc !j b = case b of
      GCons k v tl | j > (0 :: Int) -> GCons k v (trunc (j - 1) tl)
      _                             -> GNil
