{-# LANGUAGE BangPatterns        #-}
{-# LANGUAGE ScopedTypeVariables #-}
-- | When each numbered pool entry is last spoken of.
--
-- "Front.Pool" holds every name, level and expression an export defines, from
-- the line that defines it to the end of the file, because nothing tells it
-- when an entry has been read for the last time.  On a large export that is the
-- dominant live set: the pool roots the whole term graph, so every proof body
-- @mathlib@ ever writes is reachable until the final line has been parsed.
-- Measured on @std@, whose expression pool has 9,396,483 entries in it, the
-- most that are ever wanted at one time is 247,920 -- **2.6%**.
--
-- This pass reads the file once and records, for each index, the last line on
-- which it appears.  "Front.Pool" then drops an entry once that line is behind
-- it, and the pool holds the working set instead of the file.
--
-- **The scan is deliberately stupid, and that is the safety argument.**  It does
-- not know the format: it treats /every run of digits anywhere on a line/ as a
-- possible reference to that index, in every pool at once.  So it cannot miss a
-- reference by misreading a field, mistaking one pool for another, or failing
-- to keep up with a format that grows a new one.  What it can do is keep an
-- entry longer than needed -- a numeric literal that happens to equal a live
-- index, a name index that collides with an expression index -- and that costs
-- memory and nothing else.  It is not free: against a scanner that reads only
-- the fields that really are references, the working set goes from 2.6% to
-- 6.2%.  It is also not close to mattering, and a wrong answer here would be a
-- spurious rejection.
--
-- The second half of the argument is in "Front.Pool": asking for an entry that
-- was dropped raises 'Front.Pool.PoolEvicted' rather than failing the file, and
-- @Main@ answers that by reading the export again with eviction off.  So this
-- module cannot change a verdict even if everything above is wrong.  It can
-- only cost a second pass that a correct scan never asks for.
module Front.Scan
  ( Deaths
  , scanDeaths
  , noDeaths
  , deathOf
  ) where

import           Control.Monad.ST        (ST, runST)
import           Data.Array.Base         (unsafeAt, unsafeRead, unsafeWrite)
import           Data.Array.ST           (STUArray, newArray)
import           Data.Array.Unboxed      (UArray, bounds)
import           Data.Array.Unsafe       (unsafeFreeze)
import qualified Data.ByteString.Char8   as B
import qualified Data.ByteString.Unsafe  as BU
import           Data.Int                (Int32)
import           Data.Word               (Word8)

-- | For each index, the number of the last line it occurs on.  'NoDeaths' is
-- the table that never lets go of anything, which is what a file too odd to
-- scan gets, and what the second attempt at a file gets.
data Deaths
  = Deaths !(UArray Int Int32)
  | NoDeaths

noDeaths :: Deaths
noDeaths = NoDeaths

-- | The last line this index may still be wanted on.  An index the scan never
-- covered is kept for ever, which is the answer that cannot be wrong.
deathOf :: Deaths -> Int -> Int
deathOf NoDeaths _ = maxBound
deathOf (Deaths a) i
  | i >= 0 && i <= snd (bounds a) = fromIntegral (unsafeAt a i)
  | otherwise                     = maxBound
{-# INLINE deathOf #-}

-- | Read the export and say when each index is last mentioned.  Lines are
-- numbered from one, as 'Front.Export.parseExport' numbers them.
--
-- An index appears in the table only if some line defines it, and the table is
-- grown to fit as those definitions go by.  That is sound in one pass because
-- the format writes a pool entry before anything that mentions it: a reference
-- on line @L@ is to an index defined above @L@, so the table already reaches
-- it.  An integer past the end of the table is therefore not an index -- it is
-- a @natVal@, a @cidx@, a field count -- and ignoring it is right.
scanDeaths :: B.ByteString -> Deaths
scanDeaths input
  | n <= 0    = NoDeaths
  | otherwise = runST (start 1024 >>= \a0 -> go 0 1 1024 0 a0)
  where
    n = B.length input

    -- One line cannot define more than one pool entry and cannot be shorter
    -- than a few bytes, so an index this far past what the file could number is
    -- an export doing something this pass was not written for.  Rather than
    -- allocate for it, stop scanning and keep everything.
    limit = max 1024 (n `div` 16)

    start :: Int -> ST s (STUArray s Int Int32)
    start c = newArray (0, c - 1) 0

    grow :: forall s. Int -> Int -> STUArray s Int Int32
         -> ST s (Int, STUArray s Int Int32)
    grow want c a = do
      let c' = until (> want) (* 2) c
      a' <- start c'
      let cp :: Int -> ST s ()
          cp !i | i >= c    = pure ()
                | otherwise = unsafeRead a i >>= unsafeWrite a' i >> cp (i + 1)
      cp 0
      pure (c', a')

    -- Cut the table down to the indices that exist, once, at the end.
    --
    -- Doubling is the right way to grow it -- the scan is a linear pass over
    -- half a gigabyte and cannot afford to copy the table often -- but it ends
    -- holding up to twice the words it needs, and unlike everything else here
    -- the table then stays live for the whole run.  On @std@ that is 67 MB
    -- held to the last line where 38 MB would do.  One more copy buys it back.
    fit :: forall s. Int -> Int -> STUArray s Int Int32
        -> ST s (STUArray s Int Int32)
    fit want c a
      | want >= c = pure a
      | otherwise = do
          a' <- start want
          let cp :: Int -> ST s ()
              cp !i | i >= want = pure ()
                    | otherwise = unsafeRead a i >>= unsafeWrite a' i >> cp (i + 1)
          cp 0
          pure a'

    -- @c@ is how many slots the table has and @hi@ the largest index any line
    -- has claimed to define, which is what the finished table has to reach;
    -- @c@ overshoots it by up to a factor of two, that being what doubling
    -- costs, and 'fit' is where that is given back.
    go :: Int -> Int -> Int -> Int -> STUArray s Int Int32 -> ST s Deaths
    go !i !ln !c !hi !a
      | i >= n = Deaths <$> (unsafeFreeze =<< fit (hi + 1) c a)
      | otherwise =
          let w = BU.unsafeIndex input i in
          if isDigit w
            then case digits i 0 of
              (v, j)
                | v >= 0 && v < c -> unsafeWrite a v (fromIntegral ln) >> go j ln c hi a
                | otherwise       -> go j ln c hi a
            else if w == wNL
              then go (i + 1) (ln + 1) c hi a
              -- @"in":@, @"il":@, @"ie":@ -- the three ways a line says which
              -- entry it is defining, and the only thing here that has to know
              -- anything about the format.  Getting this wrong makes the table
              -- too small, which keeps entries rather than losing them.
              else if w == wQuote && i + 5 < n
                      && BU.unsafeIndex input (i + 1) == wI
                      && isPoolTag (BU.unsafeIndex input (i + 2))
                      && BU.unsafeIndex input (i + 3) == wQuote
                      && BU.unsafeIndex input (i + 4) == wColon
                then case digits (i + 5) 0 of
                  (v, _)
                    | v >= c && v <= limit ->
                        grow v c a >>= \(c', a') -> go (i + 1) ln c' (max hi v) a'
                    | v > limit            -> pure NoDeaths
                    | otherwise            -> go (i + 1) ln c (max hi v) a
                else go (i + 1) ln c hi a

    -- The value of the run of digits at @i@, and where it ends.  A run too long
    -- to be an index saturates: it is a literal, and all the caller does with it
    -- is decline to record it.
    digits :: Int -> Int -> (Int, Int)
    digits !i !acc
      | i < n && isDigit w = digits (i + 1) (if acc > limit then acc
                                             else acc * 10 + fromIntegral (w - w0))
      | otherwise          = (acc, i)
      where w = BU.unsafeIndex input i

isDigit :: Word8 -> Bool
isDigit w = w >= 48 && w <= 57
{-# INLINE isDigit #-}

isPoolTag :: Word8 -> Bool
isPoolTag w = w == 110 || w == 108 || w == 101   -- n, l, e
{-# INLINE isPoolTag #-}

w0, wNL, wQuote, wColon, wI :: Word8
w0     = 48
wNL    = 10
wQuote = 34
wColon = 58
wI     = 105
