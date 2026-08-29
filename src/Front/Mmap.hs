{-# LANGUAGE CApiFFI #-}
-- | Getting the export into memory without putting it on the heap.
--
-- 'Data.ByteString.readFile' is the obvious way to read the file and the wrong
-- one for this shape of program, for a reason that has nothing to do with how
-- fast it is.  A 'B.ByteString' is a window on a buffer, and every window keeps
-- the whole buffer: the parser's unread remainder is @B.drop k input@, so the
-- entire file is reachable until the last line has been read -- and the last
-- line has been read at exactly the moment the run holds the most other things
-- as well.  Measured by closure type on @std@, whose export is 526 MiB, the
-- peak live set is 1.56 GiB of which @ARR_WORDS@ is 526.2 MiB: the file, to the
-- megabyte, a third of everything alive.  On @mathlib@ it is 5.64 GB of 11.63.
--
-- Copying the pieces that are kept does not fix this, because it is not the
-- pieces that are the problem; one surviving window would do, and the parse
-- state is one.  Reading the file in chunks would fix it, and would mean a
-- reader that no longer sees the file as a single string.
--
-- Mapping it fixes it and costs eleven lines.  The bytes are then file-backed
-- pages rather than heap: the garbage collector never copies them, @-M@ never
-- counts them, and the kernel may drop any of them at any time and fetch them
-- again from a file that is still there.  So the file stops being a term in the
-- live set, and a box with less memory than the export is big is no longer a
-- contradiction.  It is also a little quicker, since nothing is copied into the
-- heap to begin with.
--
-- The map has no finalizer and is never unmapped.  That is deliberate rather
-- than lazy: slices of it outlive every scope that could sensibly own it, the
-- process reads one file and exits, and an unmap that happened early would be a
-- segmentation fault rather than a leak.
--
-- Nothing here is required for correctness.  'readExport' falls back to reading
-- the file the ordinary way if any of it fails or is unavailable, which is what
-- a platform without @mmap@ looks like from here.
module Front.Mmap
  ( readExport
  ) where

import           Control.Exception        (SomeException, try)
import qualified Data.ByteString.Char8    as B
import qualified Data.ByteString.Internal as BI
import           Data.Word                (Word8)
import           Foreign.C.String         (withCString)
import           Foreign.C.Types          (CInt (..), CLong (..), CSize (..))
import           Foreign.ForeignPtr       (newForeignPtr_)
import           Foreign.Ptr              (Ptr, nullPtr, ptrToIntPtr)
import           System.IO                (IOMode (..), hFileSize, withBinaryFile)

foreign import capi unsafe "fcntl.h open"
  c_open :: Ptr a -> CInt -> IO CInt

foreign import capi unsafe "unistd.h close"
  c_close :: CInt -> IO CInt

foreign import capi unsafe "sys/mman.h mmap"
  c_mmap :: Ptr Word8 -> CSize -> CInt -> CInt -> CInt -> CLong -> IO (Ptr Word8)

foreign import capi unsafe "sys/mman.h madvise"
  c_madvise :: Ptr Word8 -> CSize -> CInt -> IO CInt

-- | The export at this path, mapped if that is possible and read if it is not.
readExport :: FilePath -> IO B.ByteString
readExport path = do
  r <- try (mapFile path)
  case r :: Either SomeException (Maybe B.ByteString) of
    Right (Just bs) -> pure bs
    _               -> B.readFile path

mapFile :: FilePath -> IO (Maybe B.ByteString)
mapFile path = do
  n <- withBinaryFile path ReadMode hFileSize
  -- A zero-length mapping is an error rather than an empty string, and an
  -- export that does not fit in an 'Int' does not fit in a 'B.ByteString'
  -- either.  Both go the ordinary way and get the ordinary diagnosis.
  if n <= 0 || n > fromIntegral (maxBound :: Int)
    then pure Nothing
    else withCString path $ \cpath -> do
      fd <- c_open cpath oRDONLY
      if fd < 0 then pure Nothing else do
        p <- c_mmap nullPtr (fromIntegral n) protREAD mapPRIVATE fd 0
        -- The mapping is independent of the descriptor once it exists.
        _ <- c_close fd
        if ptrToIntPtr p == (-1)
          then pure Nothing
          else do
            -- Both readers of this map go through it front to back and never
            -- come back, so say so and let the kernel read ahead in the shape
            -- the reading has.  It is a hint and is treated as one: on a box
            -- with memory to spare the pages stay resident either way, and on
            -- @mathlib@ 5.5 GB of the process's 18.7 GB is this file.  That
            -- 5.5 GB is not a requirement, which is the point of the mapping --
            -- the pages are clean and file-backed, so a kernel that needs the
            -- memory takes them back rather than the process dying for them.
            _ <- c_madvise p (fromIntegral n) madvSEQUENTIAL
            fp <- newForeignPtr_ p
            pure (Just (BI.fromForeignPtr fp 0 (fromIntegral n)))
  where
    oRDONLY        = 0
    protREAD       = 1
    mapPRIVATE     = 2
    madvSEQUENTIAL = 2
