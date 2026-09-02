{-# LANGUAGE BangPatterns #-}
-- | The numbered pools an export stream builds its names, levels and
-- expressions in.
--
-- A pool is written once, left to right, and read only backwards: a line
-- defines the entry at some index and may mention any index already defined.
--
-- The thing that decides the shape of this module is that a pool is also a
-- /root/.  Whatever it holds, the garbage collector holds: an expression filed
-- at index 40,000,000 keeps its whole subterm graph, and the pool that never
-- lets go of anything therefore keeps every proof body in the file until the
-- last line has been read.  On @mathlib@ that was most of an eleven gigabyte
-- live set, and it is why reading the file and checking it at the same time
-- /helped/ -- finishing the read early was the only way the pool ever died.
--
-- So an entry is dropped once "Front.Scan" says nothing below can ask for it
-- again.  The working set is small: of @std@'s 9,396,483 expressions the most
-- ever wanted at one time is 247,920, and with the conservative scan that
-- module actually uses, 579,917 -- six per cent.  What is held is then the
-- terms being worked on rather than the terms that have ever been read.
--
-- The layout follows from that. Two chunks of the most recent entries are kept
-- as plain lists, because that is where the references are -- 40% of them in
-- @std@ are to the entry immediately before, and 55% within the last
-- sixty-four -- and a list of sixty-four costs nothing to build and is walked
-- in a handful of loads.  An entry falling out the back of the second chunk is
-- looked up in the table: if it is dead it is dropped there and then and never
-- costs a map insertion at all, and only the survivors go into the 'IntMap'
-- behind.  Since most entries are dead by then, most are never filed twice.
--
-- The general case is not given up on.  Indices in the format are sparse and
-- need not be monotonic; a pool handed one out of turn turns into the plain
-- map, which is the old behaviour.  No export a real exporter writes does this.
--
-- An earlier version of this module stored the whole pool densely, in chunks
-- hung in a sixty-four-way trie, and was measurably quicker at reading than the
-- 'IntMap' it replaced.  That is given up here, and knowingly: the map now
-- holds the live minority rather than the file, so it is a fraction of the size
-- it was measured at, and what it costs in reading it returns several times
-- over in what the collector no longer has to trace.
module Front.Pool
  ( Pool
  , PoolEvicted (..)
  , emptyPool
  , poolPush
  , poolAt
  , poolReap
  ) where

import           Control.Exception  (Exception, throw)
import           Data.Bits          (shiftL, (.&.))
import           Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IM
import           Data.List          (foldl')
import           Front.Scan         (Deaths, deathOf)

-- | Asking for an entry that was dropped.
--
-- This is a bug in "Front.Scan" and nothing else -- a reference it did not see
-- -- and it is raised rather than reported so that no verdict can rest on it.
-- @Main@ answers it by reading the export again with eviction off, which is the
-- behaviour this module had before eviction existed.  The cost of being wrong
-- here is therefore a second pass, not a wrong answer.
newtype PoolEvicted = PoolEvicted Int
  deriving (Show)

instance Exception PoolEvicted

-- | Entries numbered from zero.
--
-- @Dense n due lost old dm cur prv@ holds the entries @0 .. n-1@ that are still
-- wanted.  @cur@ is the chunk being filled and @prv@ the one before it, both
-- newest first; @old@ is everything below them that survived; @dm@ says which
-- line each of those dies on, so that reaping is a walk of the front of a map
-- rather than a search.  @lost@ records whether anything has been dropped,
-- which is the one thing the sparse fallback needs to know.
--
-- @due@ is the smallest key in @dm@, or 'maxBound' when nothing is waiting to
-- die.  It is redundant, and it is here because without it every line of the
-- export pays to find it again: 'poolReap' runs on all three pools after every
-- line, almost always with nothing to do, and 'IM.minViewWithKey' answers "what
-- is the smallest key" by /deleting/ that key and rebuilding the spine above it.
-- On @std@ that was 7.5% of everything the run allocated, thrown away
-- immediately, to learn an 'Int' that had not changed.
data Pool a
  = Dense {-# UNPACK #-} !Int {-# UNPACK #-} !Int !Bool
          !(IntMap a) !(IntMap [Int]) ![a] ![a]
  | Sparse !(IntMap a)

-- | How many entries one chunk holds.  Big enough to cover the references that
-- never reach the map, small enough that walking one is not a search.
chunkBits :: Int
chunkBits = 6

chunkSize :: Int
chunkSize = 1 `shiftL` chunkBits

chunkMask :: Int
chunkMask = chunkSize - 1

emptyPool :: Pool a
emptyPool = Dense 0 maxBound False IM.empty IM.empty [] []

-- | File an entry at an index, on this line.  Strict in the entry.
--
-- The table and the line are wanted not for the entry going in but for the one
-- coming out of the back of @prv@, which is the moment its fate is decided.
poolPush :: Deaths -> Int -> Int -> a -> Pool a -> Pool a
poolPush ds line k !x (Dense n due lost old dm cur prv)
  | k == n =
      let n'   = n + 1
          cur' = x : cur
      in if n' .&. chunkMask == 0
           then case retire ds line (n' - 2 * chunkSize) prv old dm due of
                  (l, old', dm', due') -> Dense n' due' (lost || l) old' dm' [] cur'
           else Dense n' due lost old dm cur' prv
poolPush _ _ k x p = Sparse (IM.insert k x (toMap p))

-- | Decide the chunk that has just fallen out of the back.  @base@ is the index
-- of its oldest entry; the list is newest first.
--
-- Every death line filed here is past the line doing the filing, so the
-- smallest one still waiting is the smallest of what was waiting and what goes
-- in -- no need to ask the map.
retire :: Deaths -> Int -> Int -> [a] -> IntMap a -> IntMap [Int] -> Int
       -> (Bool, IntMap a, IntMap [Int], Int)
retire ds line base prv old dm due0 = go (base + length prv - 1) prv False old dm due0
  where
    go _ []         !l !o !d !u = (l, o, d, u)
    go !i (v : vs)  !l !o !d !u
      | dth <= line     = go (i - 1) vs True o d u
      -- Never spoken of again by anything the scan could see, so there is no
      -- line to reap it on and no reason to take up room in the death index.
      | dth == maxBound = go (i - 1) vs l (IM.insert i v o) d u
      | otherwise       = go (i - 1) vs l (IM.insert i v o)
                                          (IM.insertWith (++) dth [i] d)
                                          (min u dth)
      where dth = deathOf ds i

-- | The entry at an index, if the format ever gave it one.
--
-- 'Nothing' is "no line has defined this", which is a malformed export and is
-- reported as one.  An index below @n@ that is not here is a different thing
-- entirely -- it existed and was dropped -- and that is not something a file
-- can be blamed for.
poolAt :: Pool a -> Int -> Maybe a
poolAt (Sparse m) i = IM.lookup i m
poolAt (Dense n _ _ old _ cur prv) i
  | i < 0 || i >= n       = Nothing
  | i >= base             = Just $! (cur !! (n - 1 - i))
  | i >= base - chunkSize = Just $! (prv !! (base - 1 - i))
  | otherwise = case IM.lookup i old of
      Just v  -> Just $! v
      Nothing -> throw (PoolEvicted i)
  where base = n - (n .&. chunkMask)

-- | Drop everything whose last line is at or behind this one.
--
-- Called once a line has been read, so an entry this line was the last to
-- mention has already been read out of the pool by the time it goes.  The
-- common case is that nothing is due, and that case is one comparison against
-- @due@ and the pool it was given, rather than a copy of anything.
poolReap :: Int -> Pool a -> Pool a
poolReap line p@(Dense n due _ old0 dm0 cur prv)
  -- @due@ is the smallest line anything is waiting to die on, so this is the
  -- whole of the common case.  Getting here the other way means @dm0@ has a key
  -- at or behind @line@, and so that at least one entry is about to go.
  | line < due = p
  | otherwise  = go old0 dm0
  where
    go !o !d = case IM.minViewWithKey d of
      Just ((k, is), d')
        | k <= line   -> go (foldl' (flip IM.delete) o is) d'
      Just ((k, _), _) -> Dense n k        True o d cur prv
      Nothing          -> Dense n maxBound True o d cur prv
poolReap _ p = p

-- | Everything in the pool as the map it would have been.
--
-- Only the sparse fallback wants this, and it wants a pool that is still whole.
-- Once anything has been dropped there is no honest answer, so it asks for the
-- pass that never drops anything instead.
toMap :: Pool a -> IntMap a
toMap (Sparse m) = m
toMap (Dense n _ lost old _ cur prv)
  | lost      = throw (PoolEvicted (-1))
  | otherwise = IM.union old (IM.fromList (down (n - 1) cur ++ down (base - 1) prv))
  where
    base = n - (n .&. chunkMask)
    down i vs = zip [i, i - 1 ..] vs
