{-# LANGUAGE BangPatterns        #-}
{-# LANGUAGE ScopedTypeVariables #-}
-- | A mutable hash table, for the checker's memo tables.
--
-- Everything "Kernel.Check" remembers is remembered in one of these: what a
-- term reduces to, what its type is, whether two terms are convertible.  They
-- are pure caches -- a missing entry costs a recomputation and nothing else --
-- and they are enormous: a single hard declaration asks and answers millions of
-- these questions, and the tables grow to match.
--
-- Which is why they are not a 'Data.IntMap.IntMap'.  A balanced tree of ten
-- million entries answers a lookup in some two dozen dependent pointer
-- dereferences, essentially all of them cache misses, and pays for an insertion
-- by copying the path it came down.  A table indexed by the low bits of the key
-- answers in one, and pays for an insertion by writing a word.  Nothing else
-- about the tables changes: the same keys, the same buckets, the same cap on how
-- long a bucket may get.
module Kernel.Cache
  ( Cache
  , newCache
  , clearCache
  , bucket
  , push
  ) where

import           Data.Array.Base (unsafeRead, unsafeWrite)
import           Data.Array.IO   (IOArray, newArray)
import           Data.Bits       (shiftL, (.&.))
import           Data.IORef      (IORef, newIORef, readIORef, writeIORef)

-- | Mask, number of live entries, slots.  The slot count is a power of two, so
-- the mask is one less than it and indexing is a bitwise and.
data Rep v = Rep !Int !Int !(IOArray Int [v])

newtype Cache v = Cache (IORef (Rep v))

-- | Small: most tables are asked a handful of questions and thrown away, and
-- the ones that are not double their way up in a few steps.
initialSlots :: Int
initialSlots = 64

-- | How many entries one slot may hold before the oldest is forgotten.
--
-- A cap is what keeps a table from growing without bound on a key that keeps
-- colliding, and it is affordable because forgetting an entry only costs the
-- work of computing it again.
slotCap :: Int
slotCap = 8

newRep :: Int -> IO (Rep v)
newRep n = Rep (n - 1) 0 <$> newArray (0, n - 1) []

newCache :: IO (Cache v)
newCache = Cache <$> (newIORef =<< newRep initialSlots)

-- | Forget everything.  Called when the environment or the universe parameters
-- change, which is when every answer in the table stops being about the right
-- question.
clearCache :: Cache v -> IO ()
clearCache (Cache ref) = writeIORef ref =<< newRep initialSlots

-- | The entries that could match this key, most recently added first.  The
-- caller compares them properly; a bucket is only a shortlist.
bucket :: Cache v -> Int -> IO [v]
bucket (Cache ref) k = do
  Rep mask _ arr <- readIORef ref
  unsafeRead arr (k .&. mask)

-- | Add an entry.  @keyOf@ recovers an entry's key, which is needed only when
-- the table doubles and everything has to be reindexed.
push :: (v -> Int) -> Cache v -> Int -> v -> IO ()
push keyOf (Cache ref) k v = do
  Rep mask n arr <- readIORef ref
  let i = k .&. mask
  old <- unsafeRead arr i
  unsafeWrite arr i (v : take (slotCap - 1) old)
  let n' = n + 1
  if n' > mask
    then grow keyOf ref mask arr
    else writeIORef ref (Rep mask n' arr)

-- | Double the table and reindex.  Amortised constant, and the entries are
-- rehung in the order they were in, so the cap keeps evicting the oldest.
grow :: forall v. (v -> Int) -> IORef (Rep v) -> Int -> IOArray Int [v] -> IO ()
grow keyOf ref mask arr = do
  let mask' = mask `shiftL` 1 + 1
  arr' <- newArray (0, mask') []
  let hang :: Int -> [v] -> IO Int
      hang !c []       = pure c
      hang !c (v : vs) = do
        let j = keyOf v .&. mask'
        b <- unsafeRead arr' j
        unsafeWrite arr' j (v : b)
        hang (c + 1) vs
      slot :: Int -> Int -> IO Int
      slot !c i
        | i > mask  = pure c
        | otherwise = do
            vs <- unsafeRead arr i
            c' <- hang c (reverse vs)
            slot c' (i + 1)
  n <- slot 0 0
  writeIORef ref (Rep mask' n arr')
