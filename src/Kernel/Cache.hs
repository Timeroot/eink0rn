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
  , Counter
  , newCounter
  , tick
  , readCounter
  , bumpCounter
  , nextCount
  , Budget
  , newBudget
  , getFuel
  , setFuel
  , getWaste
  , setWaste
  ) where

import           Data.Array.Base (unsafeRead, unsafeWrite)
import           Data.Array.IO   (IOArray, IOUArray, newArray)
import           Data.Bits       (shiftL, (.&.))
import           Data.IORef      (IORef, newIORef, readIORef, writeIORef)

-- | The mask and the number of live entries, then the slots.  The slot count is
-- a power of two, so the mask is one less than it and indexing is a bitwise and.
--
-- The two numbers are a pair of machine words rather than fields of a record
-- beside the array, because an insertion changes nothing else: holding them in
-- a boxed cell meant building a fresh one for every entry, which for a table
-- written tens of millions of times a run came to more litter than the entries.
-- The array still needs a cell of its own, since growing the table replaces it.
data Cache v = Cache !(IOUArray Int Int) !(IORef (IOArray Int [v]))

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

newCache :: IO (Cache v)
newCache = do
  hdr <- newArray (0, 1) 0
  unsafeWrite hdr 0 (initialSlots - 1)
  arr <- newArray (0, initialSlots - 1) []
  Cache hdr <$> newIORef arr

-- | Forget everything.  Called when the environment or the universe parameters
-- change, which is when every answer in the table stops being about the right
-- question.
clearCache :: Cache v -> IO ()
clearCache (Cache hdr ref) = do
  unsafeWrite hdr 0 (initialSlots - 1)
  unsafeWrite hdr 1 0
  writeIORef ref =<< newArray (0, initialSlots - 1) []

-- | The entries that could match this key, most recently added first.  The
-- caller compares them properly; a bucket is only a shortlist.
bucket :: Cache v -> Int -> IO [v]
bucket (Cache hdr ref) k = do
  mask <- unsafeRead hdr 0
  arr  <- readIORef ref
  unsafeRead arr (k .&. mask)

-- | Add an entry.  @keyOf@ recovers an entry's key, which is needed only when
-- the table doubles and everything has to be reindexed.
push :: (v -> Int) -> Cache v -> Int -> v -> IO ()
push keyOf c@(Cache hdr ref) k v = do
  mask <- unsafeRead hdr 0
  n    <- unsafeRead hdr 1
  arr  <- readIORef ref
  let i = k .&. mask
  old <- unsafeRead arr i
  unsafeWrite arr i (v : capped old)
  let n' = n + 1
  if n' > mask then grow keyOf c mask arr
               else unsafeWrite hdr 1 n'

-- | The bucket, shortened to leave room for one more entry.
--
-- @take@ would say this, and would also copy a bucket that is already short
-- enough -- which, at a load factor of one, is almost every bucket there is.
capped :: [v] -> [v]
capped vs = if fits (slotCap - 1) vs then vs else take (slotCap - 1) vs
  where
    fits _ []       = True
    fits 0 _        = False
    fits j (_ : xs) = fits (j - 1 :: Int) xs

-- | Double the table and reindex.  Amortised constant, and the entries are
-- rehung in the order they were in, so the cap keeps evicting the oldest.
grow :: forall v. (v -> Int) -> Cache v -> Int -> IOArray Int [v] -> IO ()
grow keyOf (Cache hdr ref) mask arr = do
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
  unsafeWrite hdr 0 mask'
  unsafeWrite hdr 1 n
  writeIORef ref arr'
{-# NOINLINE grow #-}

-- | A countdown that lives outside the checker's state.
--
-- "Kernel.Check" charges every reduction step, and the state it charges it to is
-- an ordinary immutable record: bumping a field in it allocates a new one, which
-- for a counter ticked tens of millions of times a declaration is the whole cost
-- of having the counter.  A one-word unboxed array is a machine word write.
newtype Counter = Counter (IOUArray Int Int)

newCounter :: Int -> IO Counter
newCounter n = Counter <$> newArray (0, 0) n

-- | Count one down, reloading and reporting 'True' on the step that reaches
-- zero.
tick :: Counter -> Int -> IO Bool
tick (Counter a) reload = do
  n <- unsafeRead a 0
  if n > 1 then unsafeWrite a 0 (n - 1) >> pure False
           else unsafeWrite a 0 reload  >> pure True

readCounter :: Counter -> IO Int
readCounter (Counter a) = unsafeRead a 0

bumpCounter :: Counter -> IO ()
bumpCounter (Counter a) = unsafeRead a 0 >>= unsafeWrite a 0 . (+ 1)

-- | Hand out the current value and move on: a supply of identifiers, none of
-- them ever returned twice.
nextCount :: Counter -> IO Int
nextCount (Counter a) = do
  n <- unsafeRead a 0
  unsafeWrite a 0 (n + 1)
  pure n

-- | The reduction budget: two words, and for the same reason 'Counter' is one.
--
-- 'Kernel.Check.spend' runs on every reduction step and changes nothing but
-- these two numbers, so keeping them among the fields of the checker's state
-- meant rebuilding a twenty-field record to subtract one from an @Int@.  They
-- are a pair rather than two 'Counter's because every reader of one is a reader
-- of the other, and one array header is cheaper than two.
--
-- Slot 0 is the fuel and slot 1 the waste allowance; see 'Kernel.Check.spend'
-- for what they mean.  Unlike the memo tables this is not a cache: what it
-- holds decides how far reduction goes, and the combinators that lend a
-- computation a budget are the ones that put the caller's back.
newtype Budget = Budget (IOUArray Int Int)

newBudget :: Int -> Int -> IO Budget
newBudget f w = do
  a <- newArray (0, 1) 0
  unsafeWrite a 0 f
  unsafeWrite a 1 w
  pure (Budget a)

getFuel :: Budget -> IO Int
getFuel (Budget a) = unsafeRead a 0

setFuel :: Budget -> Int -> IO ()
setFuel (Budget a) = unsafeWrite a 0

getWaste :: Budget -> IO Int
getWaste (Budget a) = unsafeRead a 1

setWaste :: Budget -> Int -> IO ()
setWaste (Budget a) = unsafeWrite a 1
