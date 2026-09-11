{-# LANGUAGE BangPatterns        #-}
{-# LANGUAGE ScopedTypeVariables #-}
-- | The checker's mutable containers: a hash table for the memo tables, a
-- dense table for the local constants, and the two counters that are hot
-- enough to be worth keeping out of the state record.
--
-- Most of what "Kernel.Check" remembers is remembered in the hash table: what a
-- term reduces to, what its type is, whether two terms are convertible.  Those
-- are pure caches -- a missing entry costs a recomputation and nothing else --
-- and they are enormous: a single hard declaration asks and answers millions of
-- these questions, and the tables grow to match.  The one thing that is not a
-- cache is what a local constant stands for, and 'Table' is where that lives.
--
-- Which is why they are not a 'Data.IntMap.IntMap'.  A balanced tree of ten
-- million entries answers a lookup in some two dozen dependent pointer
-- dereferences, essentially all of them cache misses, and pays for an insertion
-- by copying the path it came down.  A table indexed by the low bits of the key
-- answers in one, and pays for an insertion by writing a word.  Nothing else
-- about the tables changes: the same keys, the same buckets, the same cap on how
-- long a bucket may get.
module Kernel.Cache
  ( Chain (..)
  , Cache
  , newCache
  , newCacheBounded
  , clearCache
  , bucket
  , push
  , Table
  , newTable
  , putTable
  , getTable
  , Counter
  , newCounter
  , tick
  , readCounter
  , writeCounter
  , bumpCounter
  , nextCount
  , Budget
  , newBudget
  , getFuel
  , setFuel
  , getWaste
  , setWaste
  ) where

import           Control.Monad   (when)
import           Data.Array.Base (getNumElements, unsafeRead, unsafeWrite)
import           Data.Array.IO   (IOArray, IOUArray, newArray)
import           Data.Bits       (shiftL, (.&.))
import           Data.IORef      (IORef, newIORef, readIORef, writeIORef)

-- | What a cache needs to know about the buckets it hangs entries in.
--
-- It does not know what an entry is.  It knows that a bucket is a chain of
-- them, newest first; everything else -- what an entry holds, what a lookup
-- matches it against -- belongs to the table's owner and is written beside it
-- in "Kernel.Check".
--
-- The point of the class is that an entry /is/ a link, rather than a value hung
-- off one.  A bucket of @[(k, ek, v)]@ is two heap objects an entry and nine
-- words with the @Int@ boxed; a chain whose links carry those fields is one
-- object of five.  The memo tables are about a fifth of the live heap at the
-- peak of a run of @std@, and the entries in them were 104 MB of conses and
-- boxed triples where they are now 55 MB of chain links, so the four words are
-- worth a class to get.
--
-- The other thing an entry now carries is its own key, which is why 'push' no
-- longer takes a function to recover one: the only caller that ever wanted a
-- key back was 'grow', and 'chainHang' is where it asks.
--
-- Nothing here says an entry's fields must be strict, and 'Kernel.Check.MemoB'
-- says at length why the largest table's are not.
class Chain b where
  -- | The empty bucket.
  chainNil  :: b
  -- | At most @n@ entries.  Must hand back the bucket it was given when that is
  -- already so: at a load factor of one nearly every bucket is short, and
  -- copying them all would cost more than the cap saves.
  chainCap  :: Int -> b -> b
  -- | Rehang a bucket's entries into the table replacing it, adding how many
  -- there were to a running count.  Oldest first, so the cap goes on forgetting
  -- the oldest.  Only 'grow' calls this.
  chainHang :: IOArray Int b -> Int -> b -> Int -> IO Int

-- | The mask, the number of live entries and the largest mask the table may
-- reach, then the slots.  The slot count is a power of two, so the mask is one
-- less than it and indexing is a bitwise and.
--
-- The two numbers are a pair of machine words rather than fields of a record
-- beside the array, because an insertion changes nothing else: holding them in
-- a boxed cell meant building a fresh one for every entry, which for a table
-- written tens of millions of times a run came to more litter than the entries.
-- The array still needs a cell of its own, since growing the table replaces it.
data Cache b = Cache !(IOUArray Int Int) !(IORef (IOArray Int b))

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

-- | A table that grows as far as it is asked to.
--
-- Right for a table whose entries are few, or bounded by something other than
-- the work done -- and for 'Kernel.Check.tcLocalId', which is a 'Cache' but not
-- a cache: see 'newCacheBounded'.
newCache :: Chain b => IO (Cache b)
newCache = newCacheWith 0

-- | A table that stops growing at the given number of slots (rounded down to a
-- power of two), and from then on forgets its oldest entry in a bucket rather
-- than making more buckets.
--
-- Every /pure/ memo wants this.  What an entry costs is not the entry: it is
-- that the table is a root, so a remembered answer keeps the term it is about
-- alive for as long as the declaration runs, and the answers are about
-- intermediate terms that nothing else refers to.  An unbounded table therefore
-- retains every intermediate result of the hardest declaration in the file, and
-- the collector walks all of it on every major GC.  Sweeping the ceiling on one
-- hard declaration of @con-leche@ -- max residency, then mutator and collector
-- time:
--
-- @
--   unbounded   11.17 GB   211s MUT   446s GC
--   65536        5.55 GB   303s MUT   403s GC
--    8192        1.45 GB   294s MUT   238s GC
--     512        0.88 GB   251s MUT    89s GC
-- @
--
-- Which says the recomputation a small table costs is real -- it is the mutator
-- column going up -- and is nowhere near what the collector charges for keeping
-- the answers.  It also says nothing about a file that is merely large, where
-- there is no runaway to contain and the recomputation is all there is; see
-- 'Kernel.Check.memoSlots' for the other half of the measurement and where the
-- two of them meet.
--
-- This is only sound for a table a miss costs nothing but time.  'newCache' is
-- for the rest.
newCacheBounded :: Chain b => Int -> IO (Cache b)
newCacheBounded n = newCacheWith (if n > 0 then pow2Below n - 1 else 0)
  where pow2Below k = let go m = if m * 2 <= k then go (m * 2) else m in go 1

newCacheWith :: Chain b => Int -> IO (Cache b)
newCacheWith ceil = do
  hdr <- newArray (0, 2) 0
  unsafeWrite hdr 0 (initialSlots - 1)
  unsafeWrite hdr 2 ceil
  arr <- newArray (0, initialSlots - 1) chainNil
  Cache hdr <$> newIORef arr

-- | Forget everything.  Called when the environment or the universe parameters
-- change, which is when every answer in the table stops being about the right
-- question.
clearCache :: Chain b => Cache b -> IO ()
clearCache (Cache hdr ref) = do
  unsafeWrite hdr 0 (initialSlots - 1)
  unsafeWrite hdr 1 0
  writeIORef ref =<< newArray (0, initialSlots - 1) chainNil

-- | The entries that could match this key, most recently added first.  The
-- caller compares them properly; a bucket is only a shortlist.
bucket :: Cache b -> Int -> IO b
bucket (Cache hdr ref) k = do
  mask <- unsafeRead hdr 0
  arr  <- readIORef ref
  unsafeRead arr (k .&. mask)

-- | Add an entry, given as the function that puts it at the front of a bucket:
-- an entry is a link of the chain, so only its owner can build one, and the
-- bucket it is to be linked onto is not known until the slot has been read.
--
-- Inlined so that the link is built where the fields are, rather than a closure
-- over them being built here.
push :: Chain b => Cache b -> Int -> (b -> b) -> IO ()
push c@(Cache hdr ref) k link = do
  mask <- unsafeRead hdr 0
  n    <- unsafeRead hdr 1
  arr  <- readIORef ref
  let i = k .&. mask
  old <- unsafeRead arr i
  unsafeWrite arr i (link (chainCap (slotCap - 1) old))
  let n' = n + 1
  if n' > mask then grow c mask arr
               else unsafeWrite hdr 1 n'
{-# INLINE push #-}

-- | Grow the table and reindex.  Amortised constant, and the entries are
-- rehung in the order they were in, so the cap keeps evicting the oldest.
--
-- By a factor of eight and not the usual two.  Doubling is what you want when
-- growing is a copy and the slots are the cost; here the slots are a word each
-- and growing is a /rehang/ -- a fresh link for every entry the table holds --
-- so the thing to minimise is how many times the entries are touched.  Ending
-- at @S@ slots, doubling rehangs about @S@ entries in total and eightfold about
-- @S/7@, and it allocates two thirds as many slots on the way.  What it costs
-- is that a table may be up to eight times larger than the entries in it need,
-- which for tables that are a word a slot and thrown away at the end of the
-- declaration is not a cost worth paying anything to avoid.
--
-- Measured on @std@, bytes allocated: doubling 114.0 GB, fourfold 112.5,
-- eightfold 112.3, sixteenfold 112.9 as the empty slots start to outweigh the
-- rehangs saved.  The clock agrees, and by more than the allocation does --
-- 155.4s, 151.2, 148.1, 146.2 -- because a rehang is also the least
-- cache-friendly thing the checker does.  Raising the load factor instead was
-- measured and rejected: at two entries a slot @std@ allocates 0.5% less and
-- runs 3% slower, the buckets having got long enough to notice.
--
-- A table at its ceiling ('newCacheBounded') declines instead, and forgets the
-- count of what it holds so as not to be asked again for another mask's worth
-- of insertions.  The count is only there to decide when to grow, so losing it
-- costs nothing; the entries stay where they are, and 'push' goes on capping
-- the buckets it writes.
grow :: forall b. Chain b => Cache b -> Int -> IOArray Int b -> IO ()
grow (Cache hdr ref) mask arr = do
 ceil <- unsafeRead hdr 2
 if ceil /= 0 && mask >= ceil then unsafeWrite hdr 1 0 else do
  let mask' = mask `shiftL` 3 + 7
  arr' <- newArray (0, mask') chainNil
  let slot :: Int -> Int -> IO Int
      slot !c i
        | i > mask  = pure c
        | otherwise = do
            b  <- unsafeRead arr i
            c' <- chainHang arr' mask' b c
            slot c' (i + 1)
  n <- slot 0 0
  unsafeWrite hdr 0 mask'
  unsafeWrite hdr 1 n
  writeIORef ref arr'
{-# NOINLINE grow #-}

-- * The local-constant table

-- | A table indexed by a dense range of small integers, written once per index
-- and never emptied.
--
-- This is what "Kernel.Check" keeps its local constants in, and a local
-- constant is not a cache entry: 'Kernel.Check.localInfo' /must/ answer, and it
-- must answer with the very binder the local was introduced with.  So none of
-- the machinery above applies -- no hashing, no buckets, no eviction, no
-- ceiling -- and what is left is an array.
--
-- The indices come from a counter that only ever goes up by one, so the array
-- can be addressed by the index itself and grown by doubling, and a lookup is
-- two loads with no arithmetic at all.
--
-- Against the 'Data.IntMap.IntMap' this replaces: an entry was a tree node, a
-- boxed key and a pair -- about 96 bytes -- and inserting one copied the path
-- down to it, some two dozen nodes of it, which on the hardest declaration in
-- the arena's @con-leche@ was tens of gigabytes of allocation for a table that
-- nothing ever reads twice.  Here an entry is a word in an array that is
-- already there, and the doubling copies about two words per entry over the
-- whole life of the table.
--
-- A chunked table -- a directory of fixed-size blocks, never copied -- was
-- written first and measured worse, because the interesting number here is not
-- the twenty million entries of one pathological declaration but the /tens of
-- thousands of tables/ a file makes, one per declaration, nearly all of them
-- holding a few dozen locals.  Giving each of those a 32 KB block up front cost
-- 6.7% of everything a 30 MB cone of @con-leche@ allocated, which is more than
-- the whole change saves.  Doubling from sixteen charges a small table for what
-- a small table holds, and the transient double-size array the large one pays
-- for at the end is eight bytes an entry, not the ninety-six that were the
-- point of the exercise.
newtype Table a = Table (IORef (IOArray Int a))

-- | Entries a new table has room for.  Small: most declarations introduce a
-- handful of locals and are never heard from again.
tableInit :: Int
tableInit = 16

-- | What an index that has never been written holds.  A lookup of one is a bug
-- in the caller, and this is how it says so; see 'Kernel.Check.localInfo' for
-- the bounds check that is supposed to make it unreachable.
unwritten :: a
unwritten = error "Kernel.Cache.getTable: index never written"

newTable :: IO (Table a)
newTable = Table <$> (newIORef =<< newArray (0, tableInit - 1) unwritten)

-- | Record what index @i@ holds, growing the table to reach it if need be.
--
-- The value is forced, because the table is a root that outlives the reduction
-- that made the entry: an unforced one would keep alive whatever the thunk
-- closed over, which for a binder's type is the term it was read out of.
putTable :: Table a -> Int -> a -> IO ()
putTable (Table ref) !i x = do
  arr <- readIORef ref
  n   <- getNumElements arr
  arr' <- if i < n then pure arr else regrow ref arr n i
  x `seq` unsafeWrite arr' i x
{-# INLINE putTable #-}

-- | What index @i@ holds.  Unchecked: the caller knows the range its indices
-- come from and is expected to have checked it -- reading past the end here is
-- reading past the end of an array.
getTable :: Table a -> Int -> IO a
getTable (Table ref) !i = do
  arr <- readIORef ref
  unsafeRead arr i
{-# INLINE getTable #-}

-- | Double until @i@ fits.  Amortised constant, and off the fast path.
regrow :: IORef (IOArray Int a) -> IOArray Int a -> Int -> Int
       -> IO (IOArray Int a)
regrow ref arr n i = do
  arr' <- newArray (0, until (> i) (* 2) n - 1) unwritten
  let copy !j = when (j < n) (unsafeRead arr j >>= unsafeWrite arr' j >> copy (j + 1))
  copy 0
  writeIORef ref arr'
  pure arr'
{-# NOINLINE regrow #-}

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

-- | Set it outright.  Not everything a machine word is good for is a count:
-- "Kernel.Check" keeps the innermost local in scope in one of these, and
-- entering a binder replaces that rather than counting anything.
writeCounter :: Counter -> Int -> IO ()
writeCounter (Counter a) = unsafeWrite a 0

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
