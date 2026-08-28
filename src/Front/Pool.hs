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
-- is then a cons cell, plus one array and one trie insertion per 'chunkSize'
-- entries.  Reading one is a walk of at most that many links if it is among the
-- most recent -- 40% of the references in @std@ are to the entry immediately
-- before, and 55% are within the last sixty-four -- and otherwise a walk of the
-- trie described below.
--
-- The general case is not given up on.  Indices in the format are sparse and
-- need not be monotonic; a pool that is handed one out of turn turns into the
-- plain map, which is exactly the old behaviour, including which of two entries
-- filed at the same index wins.  No export a real exporter writes does this.
--
-- Measured on @std@, over five interleaved pairs of two binaries differing in
-- this module and nothing else: a single-threaded pass one falls from 14.6 to
-- 13.3 seconds of CPU, and every pair agreed.  It costs four per cent more
-- allocation, which is the path copying described under 'Node'.
module Front.Pool
  ( Pool
  , emptyPool
  , poolPush
  , poolAt
  ) where

import           Data.Array         (Array, elems, listArray, (!), (//))
import           Data.Bits          (shiftL, shiftR, (.&.))
import           Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IM

-- | Entries numbered from zero.
--
-- @Dense n sh root tl@ holds the entries @0 .. n-1@: the full chunks in the
-- trie @root@ reads at shift @sh@, and the rest in @tl@, newest first.  @tl@
-- therefore holds @n `mod` chunkSize@ entries, which is what lets the split
-- point be recovered from @n@ alone.
data Pool a
  = Dense {-# UNPACK #-} !Int {-# UNPACK #-} !Int !(Array Int (Node a)) [a]
  | Sparse !(IntMap a)

-- | A node of the trie the full chunks hang in: a chunk itself at the bottom,
-- and 'branchSize' children above it.
--
-- The trie is keyed by chunk number and it is /complete/ -- chunk numbers are
-- handed out in order from zero -- so the depth is fixed by how many chunks
-- there are and the path to one is its chunk number read 'branchBits' at a
-- time.  Which is the whole reason it is here rather than an 'IntMap': a map
-- keyed by chunk number branches on one bit at a time, so reaching the hundred
-- and forty-five thousandth chunk of @std@ costs seventeen dependent loads
-- through seventeen separate five-word nodes, and a third of an export's
-- references are far enough back to pay that in full.  Sixty-four-way branching
-- makes it three loads, the first two of them off nodes small and hot enough to
-- stay in cache.
--
-- What it costs is the writing: a chunk is filed by copying the path down to
-- it, three arrays of sixty-four pointers, against seventeen nodes of five
-- words for the map.  That is three times the words, once per sixty-four
-- entries, and it buys a fourfold shorter read on every one of them.
data Node a
  = Chunk !(Array Int a)
  | Branch !(Array Int (Node a))

-- | How many entries one chunk holds.  Big enough that the per-chunk costs are
-- divided by something, small enough that walking the unfrozen one is not a
-- search.
chunkBits :: Int
chunkBits = 6

chunkSize :: Int
chunkSize = 1 `shiftL` chunkBits

chunkMask :: Int
chunkMask = chunkSize - 1

-- | How many children a trie node has.  Also six, but for its own reason: a
-- node is then one cache line of pointers, and the depth for any pool an export
-- can produce is at most four.
branchBits :: Int
branchBits = 6

branchSize :: Int
branchSize = 1 `shiftL` branchBits

branchMask :: Int
branchMask = branchSize - 1

-- | A node array with nothing in it yet.  The slots are never read before they
-- are written -- 'poolAt' looks below @n@ and every chunk below @n@ is filed --
-- so what they hold is a statement of that invariant rather than a value.
emptyBranch :: Array Int (Node a)
emptyBranch = listArray (0, branchMask) (replicate branchSize unwritten)

unwritten :: Node a
unwritten = error "Front.Pool: chunk read before it was written"

emptyPool :: Pool a
emptyPool = Dense 0 0 emptyBranch []

-- | The chunk with this number.  It must be one that has been filed.
chunkAt :: Int -> Array Int (Node a) -> Int -> Array Int a
chunkAt sh0 root cn = down (sh0 - branchBits) (root ! ((cn `shiftR` sh0) .&. branchMask))
  where
    down !sh nd = case nd of
      Chunk c  -> c
      Branch a -> down (sh - branchBits) (a ! ((cn `shiftR` sh) .&. branchMask))

-- | File a chunk under the next chunk number, growing the trie by a level when
-- the number no longer fits.
--
-- Whether the subtree a chunk goes into already exists is not looked up: chunk
-- numbers arrive in order, so the subtree at depth @sh@ is new exactly when the
-- bits of @cn@ below @sh@ are all zero.
pushChunk :: Int -> Array Int (Node a) -> Int -> Array Int a
          -> (Int, Array Int (Node a))
pushChunk sh root cn c
  | cn >= branchSize `shiftL` sh =
      let sh'   = sh + branchBits
          root' = emptyBranch // [(0, Branch root)]
      in (sh', ins sh' root')
  | otherwise = (sh, ins sh root)
  where
    ins !s a
      | s == 0    = a // [(i, Chunk c)]
      | otherwise = a // [(i, Branch (ins (s - branchBits) sub))]
      where
        i = (cn `shiftR` s) .&. branchMask
        sub | cn .&. ((1 `shiftL` s) - 1) == 0 = emptyBranch
            | otherwise = case a ! i of
                Branch b -> b
                Chunk _  -> emptyBranch   -- unreachable: a chunk hangs at s == 0

-- | File an entry at an index.  Strict in the entry, as the map it replaces
-- was.
poolPush :: Int -> a -> Pool a -> Pool a
poolPush k !x (Dense n sh root tl)
  | k == n =
      let n'  = n + 1
          tl' = x : tl
      in if n' .&. chunkMask == 0
           then case pushChunk sh root (n' `shiftR` chunkBits - 1) (freeze tl') of
                  (sh', root') -> Dense n' sh' root' []
           else Dense n' sh root tl'
  where freeze vs = listArray (0, chunkMask) (reverse vs)
poolPush k x p = Sparse (IM.insert k x (toMap p))

-- Every entry is in whnf already -- 'poolPush' saw to that -- so the @$!@ costs
-- nothing and saves the thunk the reader would otherwise wrap around each of
-- the twenty-two million lookups an export of @std@ makes.
poolAt :: Pool a -> Int -> Maybe a
poolAt (Sparse m) i = IM.lookup i m
poolAt (Dense n sh root tl) i
  | i < 0 || i >= n            = Nothing
  | i >= n - (n .&. chunkMask) = Just $! (tl !! (n - 1 - i))
  | otherwise = Just $! (chunkAt sh root (i `shiftR` chunkBits)
                           ! (i .&. chunkMask))

-- | Everything in the pool as the map it would have been.
toMap :: Pool a -> IntMap a
toMap (Sparse m) = m
toMap (Dense n sh root tl) =
  IM.fromDistinctAscList (zip [0 ..] (frozen ++ reverse tl))
  where
    frozen = concat [ elems (chunkAt sh root cn) | cn <- [0 .. n `shiftR` chunkBits - 1] ]
