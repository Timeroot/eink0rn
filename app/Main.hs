-- | @eink0rn [OPTIONS] FILE.ndjson@ -- accept or reject an exported Lean
-- environment.
module Main (main) where

import           Control.Concurrent    (forkIO, killThread, threadDelay)
import           Control.Monad         (forever, when)
import qualified Data.ByteString.Char8 as B
import           Data.IORef            (modifyIORef', newIORef, readIORef,
                                        writeIORef)
import           Data.List             (isPrefixOf)
import           Front.Export          (parseExport)
import           Front.Lower           (Config (..), Progress (..),
                                        checkExportTrace, checkStdPins,
                                        defaultConfig)
import           GHC.Clock             (getMonotonicTime)
import           Kernel.Env            (AccelMode (..), Env)
import           Kernel.Name           (showName)
import           Numeric               (showFFloat)
import           System.Environment    (getArgs, getProgName)
import           System.Exit           (ExitCode (..), exitFailure, exitSuccess,
                                        exitWith)
import           System.IO             (BufferMode (..), char8, hPutStrLn,
                                        hSetBuffering, hSetEncoding, stderr,
                                        stdout)

-- | How a failed @--pin-std@ audit is reported.
data PinMode = PinOff | PinWarn | PinError
  deriving Eq

data Options = Options
  { optAccel    :: AccelMode
  , optSeal     :: Bool
    -- ^ discard a theorem's value once it has been checked, where sound
  , optPin      :: PinMode
  , optMutUniv  :: Bool
    -- ^ reject a mutual inductive block whose types land in different universes
  , optProgress :: Maybe Double
    -- ^ report progress on stderr, naming any declaration that took at least
    -- this many seconds
  , optFile     :: Maybe String
  }

defaults :: Options
defaults = Options AccelCanonical True PinOff False Nothing Nothing

usage :: String -> String
usage prog = unlines
  [ "usage: " ++ prog ++ " [OPTIONS] FILE.ndjson"
  , ""
  , "  --nat-accel=MODE   when to compute Nat operations on bignums"
  , "      canonical        only for declarations matching the stored"
  , "                       canonical specification exactly (default)"
  , "      verified         for any declaration whose own defining equations"
  , "                       say it computes the operation"
  , "      off              never; unfold everything the slow way"
  , "      always           on the strength of the name alone.  UNSOUND, and"
  , "                       provided for comparison with kernels that do this"
  , ""
  , "  --keep-proofs      keep the value of every theorem after checking it."
  , "                     By default a theorem whose statement no reduction"
  , "                     rule could ever look inside becomes an axiom, and"
  , "                     is never unfolded again"
  , ""
  , "  --pin-std=LEVEL    audit False, Eq, Iff, Nonempty, the quotient package"
  , "                     and the three axioms against their standard forms"
  , "      off              do not audit (default)"
  , "      warn             report mismatches on stderr, but accept"
  , "      error            reject the file on a mismatch"
  , ""
  , "  --enforce-mutual-univ"
  , "                     reject a mutual inductive block whose types do not"
  , "                     all land in the same universe, as every other Lean"
  , "                     kernel does.  By default such a block is accepted"
  , "                     when it can be derived from simpler types (SPEC §9.6)"
  , ""
  , "  --progress[=SECS]  report progress on stderr: a running count, and a"
  , "                     line naming every declaration that took at least"
  , "                     SECS seconds on its own (default 1)"
  ]

parseArgs :: [String] -> Either String Options
parseArgs = foldl step (Right defaults)
  where
    step acc arg = acc >>= \o -> case arg of
      _ | arg `elem` ["-h", "--help"] -> Left ""
        | Just v <- stripFlag "--nat-accel=" arg -> (\m -> o { optAccel = m }) <$> accel v
        | Just v <- stripFlag "--pin-std="   arg -> (\m -> o { optPin   = m }) <$> pin v
        | arg == "--keep-proofs" -> Right o { optSeal = False }
        | arg == "--enforce-mutual-univ" -> Right o { optMutUniv = True }
        | arg == "--progress" -> Right o { optProgress = Just 1 }
        | Just v <- stripFlag "--progress="  arg -> (\s -> o { optProgress = Just s }) <$> secs v
        | "-" `isPrefixOf` arg -> Left ("unknown option: " ++ arg)
        | Just f <- optFile o  -> Left ("more than one input file: " ++ f ++ ", " ++ arg)
        | otherwise            -> Right o { optFile = Just arg }

    stripFlag p s = if p `isPrefixOf` s then Just (drop (length p) s) else Nothing

    accel v = case v of
      "canonical" -> Right AccelCanonical
      "verified"  -> Right AccelVerified
      "off"       -> Right AccelOff
      "always"    -> Right AccelAlways
      _           -> Left ("unknown --nat-accel mode: " ++ v)

    pin v = case v of
      "off"   -> Right PinOff
      "warn"  -> Right PinWarn
      "error" -> Right PinError
      _       -> Left ("unknown --pin-std level: " ++ v)

    secs v = case reads v of
      [(s, "")] | s >= 0 -> Right s
      _                  -> Left ("not a number of seconds: " ++ v)

main :: IO ()
main = do
  -- A 'Kernel.Name.Name' holds the bytes the export file held, undecoded: the
  -- kernel never looks inside one except to compare it, and a byte string
  -- compares the same either way.  Diagnostics have to put those bytes back on
  -- the wire unchanged, or a name like @α@ comes out re-encoded twice.  A
  -- byte-transparent handle is the whole fix; everything the checker writes
  -- itself is ASCII.
  mapM_ (`hSetEncoding` char8) [stdout, stderr]
  -- @--progress@ is only useful if it arrives while the run is still going, and
  -- a redirected handle blocks by default.
  hSetBuffering stderr LineBuffering
  args <- getArgs
  prog <- getProgName
  case parseArgs args of
    Left ""  -> putStr (usage prog) >> exitSuccess
    Left err -> die (err ++ "\n" ++ usage prog)
    Right o  -> case optFile o of
      Nothing   -> die (usage prog)
      Just path -> run o path
  where
    die msg = hPutStrLn stderr msg >> exitWith (ExitFailure 2)

run :: Options -> String -> IO ()
run o path = do
  input <- B.readFile path
  let cfg = defaultConfig { cfgAccel = optAccel o, cfgSealProofs = optSeal o
                          , cfgMutUniv = optMutUniv o }
  result <- case parseExport input of
    Left err -> pure (Left err)
    Right ds -> walk o (checkExportTrace cfg ds)
  case result of
    Left err  -> reject err
    Right env -> case if optPin o == PinOff then [] else checkStdPins env of
      []   -> accept
      msgs -> case optPin o of
        PinError -> reject (unlines' msgs)
        _        -> do mapM_ (hPutStrLn stderr . ("warning: " ++)) msgs
                       accept
  where
    accept     = putStrLn "ACCEPT" >> exitSuccess
    reject err = do putStrLn "REJECT"
                    hPutStrLn stderr err
                    exitFailure
    unlines' = foldr1 (\a b -> a ++ "\n" ++ b)

-- | Drive the trace to its verdict.
--
-- Without @--progress@ this is a plain fold and costs a clock read per
-- declaration at most; with it, every declaration is timed and the slow ones are
-- named.
walk :: Options -> [Progress] -> IO (Either String Env)
walk o ps0 = case optProgress o of
    Nothing  -> pure (quiet ps0)
    Just cut -> do
      t0  <- getMonotonicTime
      n   <- newIORef (0 :: Int)
      cur <- newIORef (Nothing, t0)
      let tally t = do
            k       <- readIORef n
            (mn, s) <- readIORef cur
            note (show k ++ " declarations, " ++ secs (t - t0) ++ " elapsed"
                  ++ if t - s < cut then ""
                       else ", " ++ secs (t - s) ++ " in " ++ nameOf mn)
      -- A file with a few tens of thousands of declarations and one that has
      -- millions both want to be heard from about as often, so the heartbeat is
      -- on the clock rather than on the count -- and on a thread rather than on
      -- the loop, because the run one most wants to hear from is the one stuck
      -- inside a single declaration, which is exactly the run whose loop has
      -- stopped coming round.
      beat <- forkIO . forever $ do
                threadDelay (round (heartbeat * 1e6))
                getMonotonicTime >>= tally
      let loud (Starting mn : ps) = do
            t <- getMonotonicTime
            writeIORef cur (mn, t)
            loud ps
          loud (Checked mn : ps) = do
            t       <- getMonotonicTime
            (_, s)  <- readIORef cur
            modifyIORef' n (+ 1)
            when (t - s >= cut) $ note (secs (t - s) ++ "  " ++ nameOf mn)
            loud ps
          loud (Failed err : _) = do
            note "stopped:"
            getMonotonicTime >>= tally
            pure (Left err)
          loud (Done env : _) = do
            getMonotonicTime >>= tally
            pure (Right env)
          loud [] = pure (Left "internal error: export trace ended")
      r <- loud ps0
      killThread beat
      pure r
  where
    quiet (Failed err  : _) = Left err
    quiet (Done env    : _) = Right env
    quiet (Starting _  : r) = quiet r
    quiet (Checked _   : r) = quiet r
    quiet []                = Left "internal error: export trace ended"

    note s = hPutStrLn stderr ("[ " ++ s ++ " ]")
    secs t = showFFloat (Just 2) t "s"
    nameOf = maybe "<block>" showName

    heartbeat :: Double
    heartbeat = 60
