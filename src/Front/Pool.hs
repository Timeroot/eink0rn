{-# LANGUAGE BangPatterns #-}
-- | The numbered pools an export stream builds its names, levels and
-- expressions in.
--
-- A pool is written once, left to right, and read only backwards: a line
-- defines the entry at some index and may mention any index already defined.
-- An 'Data.IntMap.IntMap' says that and is the obvious thing to reach for, but
-- it pays for the writing in a way this shape does not have to.  Every
-- insertion copies the path it came down -- some two dozen nodes, six words
-- each, for a pool with nine million entries in it -- and an export of @std@
-- performs nine million of them.  Reading the pools was costing more than
-- reducing the terms they held.
--
-- So the dense case is stored densely: entries are collected into a small
-- chunk, and a chunk is frozen into an array once it is full.  Writing an entry
-- is then a cons cell, plus one array and one map insertion per 'chunkSize'
-- entries.  Reading one is a walk of at most that many links if it is among the
-- most recent -- which is what a reference in an export almost always is -- and
-- otherwise a map lookup no deeper than the one it replaces, over a map with
-- 'chunkSize' times fewer keys in it.
--
-- The general case is not given up on.  Indices in the format are sparse and
-- need not be monotonic; a pool that is handed one out of turn turns into the
-- plain map, which is exactly the old behaviour, including which of two entries
-- filed at the same index wins.  No export a real exporter writes does this.
module Front.Pool
  ( Pool
  , emptyPool
  , poolPush
  , poolAt
  ) where

import           Data.Array         (Array, elems, listArray, (!))
import           Data.Bits          (shiftL, shiftR, (.&.))
import           Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IM

-- | Entries numbered from zero.
--
-- @Dense n cs tl@ holds the entries @0 .. n-1@: the full chunks in @cs@, keyed
-- by chunk number, and the rest in @tl@, newest first.  @tl@ therefore holds
-- @n `mod` chunkSize@ entries, which is what lets the split point be recovered
-- from @n@ alone.
data Pool a
  = Dense !Int !(IntMap (Array Int a)) [a]
  | Sparse !(IntMap a)

-- | Big enough that the per-chunk costs are divided by something, small enough
-- that walking one is not a search.
chunkBits :: Int
chunkBits = 6

chunkSize :: Int
chunkSize = 1 `shiftL` chunkBits

chunkMask :: Int
chunkMask = chunkSize - 1

emptyPool :: Pool a
emptyPool = Dense 0 IM.empty []

-- | File an entry at an index.  Strict in the entry, as the map it replaces
-- was.
poolPush :: Int -> a -> Pool a -> Pool a
poolPush k !x (Dense n cs tl)
  | k == n =
      let n'  = n + 1
          tl' = x : tl
      in if n' .&. chunkMask == 0
           then Dense n' (IM.insert (n' `shiftR` chunkBits - 1) (freeze tl') cs) []
           else Dense n' cs tl'
  where freeze vs = listArray (0, chunkMask) (reverse vs)
poolPush k x p = Sparse (IM.insert k x (toMap p))

poolAt :: Pool a -> Int -> Maybe a
poolAt (Sparse m) i = IM.lookup i m
poolAt (Dense n cs tl) i
  | i < 0 || i >= n     = Nothing
  | i >= n - (n .&. chunkMask) = Just (tl !! (n - 1 - i))
  | otherwise = case IM.lookup (i `shiftR` chunkBits) cs of
      Just c  -> Just (c ! (i .&. chunkMask))
      Nothing -> Nothing            -- unreachable: every chunk below n is full

-- | Everything in the pool as the map it would have been.
toMap :: Pool a -> IntMap a
toMap (Sparse m)         = m
toMap (Dense _ cs tl)    =
  IM.fromDistinctAscList (zip [0 ..] (concatMap elems (IM.elems cs) ++ reverse tl))
