-- | @eink0rn [OPTIONS] FILE.ndjson@ -- accept or reject an exported Lean
-- environment.
module Main (main) where

import           Control.Concurrent    (forkIO, killThread, threadDelay)
import           Control.Exception     (AsyncException (..), SomeException,
                                        catch, displayException, fromException,
                                        throwIO)
import           Control.Monad         (forever, when)
import qualified Data.ByteString.Char8 as B
import           Data.IORef            (modifyIORef', newIORef, readIORef,
                                        writeIORef)
import           Data.List             (isPrefixOf)
import           Data.Maybe            (isJust)
import           Front.Export          (parseExport)
import           Front.Lower           (Config (..), Obligation (..),
                                        Progress (..), checkExportTrace,
                                        checkStdPins, defaultConfig, discharge)
import           GHC.Clock             (getMonotonicTime)
import           GHC.Conc              (getNumProcessors, par, pseq,
                                        setNumCapabilities)
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
  , optJobs     :: Maybe Int
    -- ^ check definition values on this many threads once the file has been
    -- walked; 'Nothing' to check each one where it stands
  , optFile     :: Maybe String
  }

defaults :: Options
defaults = Options AccelCanonical True PinOff False Nothing Nothing Nothing

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
  , ""
  , "  -jN                check the file in two passes, the second on N threads"
  , "                     (N omitted: one per core; -j1 for the two passes on"
  , "                     one).  Pass one only reads each declaration into the"
  , "                     environment; pass two checks it, which is where all"
  , "                     but a few per cent of the time goes and which nothing"
  , "                     else depends on.  The verdict is the same either"
  , "                     way, and pass one is now the slower of reading the"
  , "                     file and walking it.  Each"
  , "                     thread wants a nursery of its own, so a large N on a"
  , "                     small machine wants a smaller one than the default"
  , "                     gigabyte: +RTS -A128m -RTS"
  , ""
  , "Exit status: 0 accepted, 1 rejected, 2 declined -- a limit given on the"
  , "command line was reached and no verdict follows -- and 3 for a fault in"
  , "the checker or in this command line."
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
        | arg == "-j" -> Right o { optJobs = Just 0 }
        | Just v <- stripFlag "-j" arg -> (\k -> o { optJobs = Just k }) <$> jobs v
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

    -- Zero means "one per core", which is what a bare @-j@ says; it is resolved
    -- in 'run', where the core count can be asked for.
    jobs v = case reads v of
      [(k, "")] | k >= 1 -> Right k
      _                  -> Left ("not a number of threads: " ++ v)

-- | The exit status says what happened, and the four possibilities are kept
-- apart on purpose.
--
--   [@0@] the file was accepted, and @ACCEPT@ is on stdout
--   [@1@] the file was rejected, and @REJECT@ is on stdout with the reason on
--         stderr.  This is a judgement about the file
--   [@2@] declined: no judgement was reached, because the run hit a limit it
--         was given rather than a fault in the file.  The only ways to get one
--         are @+RTS -M@ and @-K@ (see 'declined')
--   [@3@] a fault in the checker, or a command line it could not read.  Not a
--         judgement about the file either, but not the file's fault
--
-- The numbering is the Lean Kernel Arena's, which reads exit 2 as declined and
-- anything above it as a checker fault.  GHC's own handler would exit 1 for an
-- uncaught exception -- indistinguishable from @REJECT@, which is the one
-- mistake worth going out of the way to avoid -- and 2 for a stack overflow,
-- which would claim a limit was reached deliberately.  So nothing is left to
-- it: 'main' catches everything and decides which of the two it was.
main :: IO ()
main = checker `catch` fault
  where
    fault :: SomeException -> IO a
    fault e
        -- exitSuccess and friends come through here; they are the answer, not
        -- a fault, and are simply passed on.
      | Just code <- fromException e = throwIO (code :: ExitCode)
      | Just HeapOverflow <- fromException e =
          declined "ran out of heap (the limit is +RTS -M)"
      | Just StackOverflow <- fromException e =
          declined "ran out of stack (the limit is +RTS -K)"
      | otherwise = do
          hPutStrLn stderr ("internal error: " ++ displayException e)
          exitWith (ExitFailure 3)

    -- Neither ACCEPT nor REJECT: the checker is not saying anything about this
    -- file.  Running out of room is a fact about the run, and reporting it as a
    -- verdict either way would be a claim the run did not establish.
    declined why = do
      putStrLn "DECLINE"
      hPutStrLn stderr (why ++ "; no verdict")
      exitWith (ExitFailure 2)

checker :: IO ()
checker = do
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
    die msg = hPutStrLn stderr msg >> exitWith (ExitFailure 3)

run :: Options -> String -> IO ()
run o path = do
  jobs <- case optJobs o of
    Nothing -> pure 0        -- one pass, no obligations, nothing to schedule
    Just 0  -> getNumProcessors
    Just k  -> pure k
  input <- B.readFile path
  let cfg = defaultConfig { cfgAccel = optAccel o, cfgSealProofs = optSeal o
                          , cfgMutUniv = optMutUniv o, cfgDefer = jobs > 0 }
  -- Forced here, rather than left as a @let@, so that there is exactly one of
  -- it.  Two threads read this list below, and they have to be reading the same
  -- one or they each read the whole file; @$!@ is what settles that, since it
  -- hands the bind an evaluated list rather than a recipe for one and the
  -- optimiser has nothing left to duplicate.  Measured on @std@: as a @let@, the
  -- reading is done twice over and the second thread buys nothing whatever.
  ds <- pure $! parseExport input
  -- Reading the file is the other half of a two-pass run's sequential part, and
  -- it does not depend on the checking, so with cores to spare it is given one.
  -- The rest are turned on here too, rather than when pass two starts, because
  -- 'sparkObs' has work for them from the first declaration onwards.
  when (jobs > 1) $ setNumCapabilities jobs >> prefetch ds
  let trace = checkExportTrace cfg ds
  walked <- walk o (if jobs > 1 then sparkObs trace else trace)
  result <- case walked of
    Left err        -> pure (Left err)
    Right (env, []) -> pure (Right env)
    Right (env, obs) -> do
      remark o (show (length obs) ++ " declarations to check on " ++ show jobs ++ " threads")
      t2 <- getMonotonicTime
      r  <- pure $! (env <$ parDischarge jobs obs)
      t3 <- getMonotonicTime
      remark o ("checked in " ++ showFFloat (Just 2) (t3 - t2) "s")
      pure r
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

-- | Read the export ahead of whoever is checking it, on a thread of its own.
--
-- 'Front.Export.parseExport' is lazy, so without this the reading happens on the
-- checker's thread, a stretch of lines at a time, in between declarations: the
-- two phases add up where they could have overlapped.  On @std@ reading takes 11
-- seconds and pass one 13, and overlapping them takes a @-j16@ run from 39
-- seconds to 27 -- most of the sequential part gone.
--
-- Nothing is communicated back, and nothing needs to be.  The list is a pure
-- value and both threads are asking it the same questions; whichever asks first
-- does the work and the other finds it done.  Should the reader fall behind, the
-- checker simply reads for itself, which is what it did before.  Should it run
-- ahead, it stops at the end of the file -- or at the first line it cannot read,
-- since that is the last element there is.
prefetch :: [a] -> IO ()
prefetch xs = () <$ forkIO (go xs)
  where
    go []       = pure ()
    go (y : ys) = y `seq` go ys

-- | Pass the trace through, setting the other threads on each obligation as
-- pass one files it rather than waiting for the end of the file.
--
-- Pass one is the sequential part of a @-jN@ run and the obligations are the
-- parallel one, so running them after it is a queue behind a bottleneck: on
-- @std@ pass one is sixteen seconds of one thread while fifteen threads have
-- nothing to do, and the obligations are a hundred and thirteen seconds of work
-- that would fit inside it seven times over.  Started here, they mostly do.
--
-- These are the same 'Obligation' values 'Done' hands back, so this decides
-- nothing: 'parDischarge' still reads every one of them, in file order, and
-- still gives the answer.  A spark that ran has left its @obCheck@ evaluated and
-- 'parDischarge' finds it done; a spark that was dropped for want of room in the
-- pool, or that never got a thread, leaves it to be done then.  Either way the
-- verdict is the one §11.6 argues for.
--
-- One spark per obligation, and no chunking, because the thunk a chunk would be
-- made of is reachable from nothing but the spark itself and would be collected
-- rather than run.  An @obCheck@ is reachable: the trace's unevaluated tail holds
-- the state that holds every obligation filed so far.  Nor does the pool overflow
-- at ninety thousand of them -- it holds four thousand, and on @std@ the threads
-- take them twice as fast as pass one can file them.
sparkObs :: [Progress] -> [Progress]
sparkObs = map fire
  where
    fire p@(Checked _ obs) = foldr (\o r -> obCheck o `par` r) p obs
    fire p                 = p

-- | Discharge the deferred obligations on @n@ threads.
--
-- An obligation is a pure @Either String ()@ and forcing it is performing it,
-- so this is 'par' and nothing more: no thread of our own, no shared state, no
-- order to get wrong.  The obligations are cut into runs of consecutive
-- declarations, each run sparked, and then read back in file order -- so the
-- answer is the first failure the sequential path would have reported, whatever
-- the sparks got up to.  Reading a run the sparks have not reached yet simply
-- evaluates it here.
--
-- Enough runs that the threads have something to steal, few enough that they
-- fit the spark pool (4096 a capability, and a spark dropped for want of room
-- is work this thread does alone).  Consecutive declarations rather than a
-- round robin so that the runs are themselves in file order, which is what
-- makes reading them back in order the same as reading the obligations back in
-- order.  Balancing does not need the round robin: the sparks are stolen as
-- threads come free, so a run that turns out to be expensive delays only
-- itself.
parDischarge :: Int -> [Obligation] -> Either String ()
parDischarge n obs
  | n <= 1    = discharge obs
  | otherwise = sparkAll runs `pseq` firstFailure runs
  where
    runs = map discharge (chunksOf size obs)
    size = max 1 ((length obs + slices - 1) `div` slices)
    slices = min 2048 (n * 64)

    -- 'par' on an element of a list the caller is still holding: a spark whose
    -- thunk nothing else can reach is collected rather than run.
    sparkAll []       = ()
    sparkAll (r : rs) = r `par` sparkAll rs

    firstFailure = foldr (>>) (Right ())

chunksOf :: Int -> [a] -> [[a]]
chunksOf _ [] = []
chunksOf k xs = case splitAt k xs of (c, rest) -> c : chunksOf k rest

-- | Say something on stderr, if the run is one that reports.
remark :: Options -> String -> IO ()
remark o s = when (isJust (optProgress o)) $ hPutStrLn stderr ("[ " ++ s ++ " ]")

-- | Drive the trace to its verdict.
--
-- Without @--progress@ this is a plain fold and costs a clock read per
-- declaration at most; with it, every declaration is timed and the slow ones are
-- named.
walk :: Options -> [Progress] -> IO (Either String (Env, [Obligation]))
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
          loud (Checked mn _ : ps) = do
            t       <- getMonotonicTime
            (_, s)  <- readIORef cur
            modifyIORef' n (+ 1)
            when (t - s >= cut) $ note (secs (t - s) ++ "  " ++ nameOf mn)
            loud ps
          loud (Failed err : _) = do
            note "stopped:"
            getMonotonicTime >>= tally
            pure (Left err)
          loud (Done env obs : _) = do
            getMonotonicTime >>= tally
            pure (Right (env, obs))
          loud [] = pure (Left "internal error: export trace ended")
      r <- loud ps0
      killThread beat
      pure r
  where
    quiet (Failed err   : _) = Left err
    quiet (Done env obs : _) = Right (env, obs)
    quiet (Starting _   : r) = quiet r
    quiet (Checked _ _  : r) = quiet r
    quiet []                 = Left "internal error: export trace ended"

    note s = hPutStrLn stderr ("[ " ++ s ++ " ]")
    secs t = showFFloat (Just 2) t "s"
    nameOf = maybe "<block>" showName

    heartbeat :: Double
    heartbeat = 60
