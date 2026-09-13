{-# LANGUAGE BangPatterns        #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE ScopedTypeVariables #-}
-- | @eink0rn [OPTIONS] FILE.ndjson@ -- accept or reject an exported Lean
-- environment.
module Main (main) where

import           Control.Concurrent    (forkIO, killThread, newChan,
                                        newEmptyMVar, putMVar, readChan,
                                        takeMVar, threadDelay, writeChan)
import           Control.Concurrent.QSemN (newQSemN, signalQSemN, waitQSemN)
import           Control.Exception     (AsyncException (..), SomeException,
                                        catch, displayException, evaluate,
                                        finally, fromException, throwIO, try)
import           Control.Monad         (forever, when)
import           Data.IORef            (atomicModifyIORef', modifyIORef',
                                        newIORef, readIORef, writeIORef)
import           Data.List             (isPrefixOf)
import           Data.Word             (Word64)
import           Data.Maybe            (isJust)
import           Front.Export          (parseExport)
import           Front.Mmap            (readExport)
import           Front.Pool            (PoolEvicted (..))
import           Front.Scan            (noDeaths, scanDeaths)
import           Front.Lower           (Config (..), Obligation (..),
                                        Progress (..), checkExportTrace,
                                        checkStdPins, defaultConfig, discharge)
import           Data.IORef            (IORef)
import           GHC.Clock             (getMonotonicTime)
import           GHC.Conc              (getNumProcessors, setNumCapabilities)
import           GHC.Stats             (RTSStats (..),
                                        getRTSStats, getRTSStatsEnabled)
import           Kernel.Env            (AccelMode (..), Env, MemoTuning (..),
                                        defaultMemoTuning)
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
    -- ^ discard every theorem's value once it has been checked
  , optPin      :: PinMode
  , optMutUniv  :: Bool
    -- ^ reject a mutual inductive block whose types land in different universes
  , optProgress :: Maybe Double
    -- ^ report progress on stderr, naming any declaration that took at least
    -- this many seconds
  , optJobs     :: Maybe Int
    -- ^ check definition values on this many threads once the file has been
    -- walked; 'Nothing' to check each one where it stands
  , optMem      :: Maybe Int
    -- ^ mebibytes of live data the threads may hold between them before they
    -- start waiting for each other; 'Nothing' to work it out from the machine,
    -- @Just 0@ not to bound it at all
  , optMemo     :: MemoTuning
    -- ^ how to size and evict the memo tables; tuning only, and no flag here can
    -- change a verdict
  , optFile     :: Maybe String
  }

defaults :: Options
defaults = Options AccelCanonical True PinOff False Nothing Nothing Nothing
                   defaultMemoTuning Nothing

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
  , "                     By default a checked theorem becomes an axiom of its"
  , "                     own statement and is never unfolded again"
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
  , "                     file and walking it.  Each thread wants a nursery of"
  , "                     its own, so a large N on a"
  , "                     small machine wants a smaller one than the default"
  , "                     gigabyte: +RTS -A128m -RTS"
  , ""
  , "  --mem=MIB          how much live data the -jN threads may hold between"
  , "                     them.  A hard declaration's memo tables can run to"
  , "                     gigabytes, so N at once can cost N times that, and"
  , "                     this is what keeps a large file from wanting more"
  , "                     memory than the machine has: a major collection that"
  , "                     finds more than this alive halves the number of"
  , "                     threads allowed to work, and one that finds"
  , "                     comfortably less gives a thread back.  It costs time"
  , "                     and never a verdict, and a file that never reaches"
  , "                     the figure is never throttled at all.  It is a bound"
  , "                     on how many run at once and so cannot bound a single"
  , "                     obligation, which on the largest exports is what the"
  , "                     peak actually is.  The default is a share of what the"
  , "                     machine reports -- the cgroup's limit where there is"
  , "                     one, since /proc/meminfo inside a container is the"
  , "                     host's memory and not the container's.  --mem=0 does"
  , "                     not bound it, and neither does a build without the"
  , "                     RTS statistics (+RTS -T), which this one has"
  , ""
  , "  --memo-slots=N     slots each bounded memo table may grow to, eight"
  , "                     entries a slot (default 4096; 0 for no ceiling).  A"
  , "                     forgotten entry costs the work of computing it again,"
  , "                     and keeping one costs the intermediate term it is"
  , "                     about, so the figure trades time against memory and"
  , "                     nothing else"
  , ""
  , "  --no-closed-memo   stop keeping answers about terms that mention no"
  , "                     local constant in tables of their own, without a"
  , "                     ceiling.  Those are the terms a declaration reduces"
  , "                     over and over, and the ones that run away mention"
  , "                     locals, so the split is on by default and this is"
  , "                     how to measure what it buys"
  , ""
  , "  --memo-lru         evict the least recently used entry of a bucket"
  , "                     rather than the oldest inserted"
  , ""
  , "To bound the whole process rather than the threads, give the RTS a ceiling"
  , "-- +RTS -M13g -RTS -- which it treats as one and not merely as a limit: it"
  , "collects the oldest generation in place above 30% of the figure and holds"
  , "the heap closer to the live set as it nears it, so a file that stays well"
  , "under is collected at the fast default.  Over it, DECLINE and exit 2."
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
        | Just v <- stripFlag "--mem=" arg -> (\m -> o { optMem = Just m }) <$> mem v
        | Just v <- stripFlag "--memo-slots=" arg ->
            (\k -> o { optMemo = (optMemo o) { mtSlots = k } }) <$> slots v
        | arg == "--no-closed-memo" -> Right o { optMemo = (optMemo o) { mtClosed = False } }
        | arg == "--memo-lru"       -> Right o { optMemo = (optMemo o) { mtLru = True } }
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

    mem v = case reads v of
      [(m, "")] | m >= 0 -> Right m
      _                  -> Left ("not a number of mebibytes: " ++ v)

    -- Zero means "no ceiling"; see 'Kernel.Cache.newCacheBounded'.
    slots v = case reads v of
      [(k, "")] | k >= 0 -> Right k
      _                  -> Left ("not a number of slots: " ++ v)

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
  budget <- case optMem o of
    Just m  -> pure (fromIntegral m * mib)
    Nothing -> memShare
  input <- readExport path
  let cfg = defaultConfig { cfgAccel = optAccel o, cfgSealProofs = optSeal o
                          , cfgMutUniv = optMutUniv o, cfgDefer = jobs > 0
                          , cfgMemo = optMemo o }
      attempt deaths = do
        -- Forced here, rather than left as a @let@, so that there is exactly
        -- one of it.  Two threads read this list below, and they have to be
        -- reading the same one or they each read the whole file; @$!@ is what
        -- settles that, since it hands the bind an evaluated list rather than a
        -- recipe for one and the optimiser has nothing left to duplicate.
        -- Measured on @std@: as a @let@, the reading is done twice over and the
        -- second thread buys nothing whatever.
        ds <- pure $! parseExport deaths input
        -- Where the walk has got to, in declarations.  Both the things that run
        -- ahead of it are held to a fixed distance of it, and this is how far
        -- they have to go.
        at <- newIORef (0 :: Int)
        -- Reading the file is the other half of a two-pass run's sequential
        -- part, and it does not depend on the checking, so with cores to spare
        -- it is given one.  The rest are turned on here too, rather than when
        -- pass two starts, because the pipeline has work for them from the
        -- first declaration onwards.
        when (jobs > 1) $ setNumCapabilities jobs >> prefetch readAhead at ds
        let trace = checkExportTrace cfg ds
        -- @-j1@ goes through the pipeline too, on one thread.  It buys no
        -- parallelism there and it is not meant to: what it buys is the same
        -- bound on the backlog, which is the whole reason to ask for one thread.
        walked <- if jobs >= 1
          then withPipeline jobs (inFlight jobs) budget
                 (\submit -> walk o submit at trace)
          else walk o (\_ -> pure ()) at trace
        case walked of
          Left err        -> pure (Left err)
          Right (env, []) -> pure (Right env)
          Right (env, obs) -> do
            -- Every obligation has been through the pipeline by now, so this is
            -- reading answers rather than working them out.  It is still what
            -- decides: the verdict is the first failure in file order, which is
            -- the sequential path's verdict whatever order the threads took.
            t2 <- getMonotonicTime
            r  <- pure $! (env <$ discharge obs)
            t3 <- getMonotonicTime
            remark o (show (length obs) ++ " obligations, read back in "
                      ++ showFFloat (Just 2) (t3 - t2) "s")
            pure r
  -- The pools drop an entry once "Front.Scan" says the file is done with it,
  -- which is what keeps a large export's live set to the terms being worked on
  -- rather than the terms ever read.  If that table is ever wrong the pool says
  -- so instead of answering, and the file is read again with the table that
  -- keeps everything -- which is what this program did before eviction existed.
  -- The answer is therefore never the scan's to give: it costs a second pass at
  -- worst, and no export has yet asked for one.
  first  <- try (attempt (scanDeaths input))
  result <- case first of
    Right r -> pure r
    Left (PoolEvicted i) -> do
      hPutStrLn stderr ("warning: dropped pool entry " ++ show i
                        ++ " was wanted after all; reading the export again"
                        ++ " with nothing dropped")
      attempt noDeaths
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

mib :: Word64
mib = 1024 * 1024

-- | Declarations the walk may be ahead of the threads.
--
-- Twice the threads: enough that a thread finishing never waits for the walk,
-- and no more, since a declaration walked and not yet checked is a
-- declaration's worth of terms nothing can collect.  Measured on @std@ at eight
-- threads, peak live: unbounded 1,159 MB, 256 waiting 950, 64 waiting 934,
-- 16 waiting 650, 8 waiting 752 -- the last being the walk holding the threads
-- up rather than the other way round.
inFlight :: Int -> Int
inFlight jobs = 2 * max 1 jobs

-- | Declarations 'prefetch' may be ahead of the walk.  Enough to cover the
-- reading of a stretch of lines, which is all the overlap there is to have.
readAhead :: Int
readAhead = 2048

-- | How much live data the threads may hold between them, on a machine that
-- says how much memory it has.
--
-- A third of it.  What the figure has to cover is not the live data but the
-- heap holding it: a copying collector wants room for a copy, so the peak is
-- something like twice the live set, and there is the nursery and the mapped
-- file besides.  A third leaves room for all of that and for whatever else the
-- machine is doing.  It is a ceiling and not a target -- nothing is allocated
-- on the strength of it, and a file whose live set never reaches it never
-- notices it is there.
--
-- A machine that does not answer gets no bound, which is what this program did
-- before the bound existed.
--
-- Two places are asked and the smaller answer wins.  @/proc/meminfo@ is the
-- machine, and inside a container it is the /host's/ machine -- the file is not
-- namespaced, so a cgroup with two gigabytes to spend on a box with a terabyte
-- reads a terabyte and sets itself a budget that would get it killed.  The
-- cgroup's own limit is the honest number where there is one, and there is not
-- always one: the file may be absent, or say @max@, or hold a placeholder near
-- @Word64@'s ceiling.  Those all mean unlimited, and unlimited means fall back
-- on the machine.
memShare :: IO Word64
memShare = do
  total <- readWord "/proc/meminfo" meminfoTotal
  v2    <- readWord "/sys/fs/cgroup/memory.max" plainNumber
  v1    <- readWord "/sys/fs/cgroup/memory/memory.limit_in_bytes" plainNumber
  -- A limit larger than the machine is not a limit; treat it as absent so that
  -- v1's "unlimited" placeholder does not have to be recognised by value.
  let capped = [ b | Just b <- [v2, v1], b > 0, maybe True (b <=) total ]
  pure $ case (total, capped) of
    (Nothing, [])  -> 0
    (t, bs)        -> minimum ([ b | Just b <- [t] ] ++ bs) `div` 3
  where
    readWord path f = do
      r <- try (readFile path)
      pure $ case r :: Either SomeException String of
        Left _  -> Nothing
        Right t -> f t
    -- Kibibytes, on the line beginning @MemTotal@.
    meminfoTotal t = case [ w | l <- lines t, "MemTotal:" `isPrefixOf` l
                              , w <- take 1 (drop 1 (words l)) ] of
      [w] | [(k, "")] <- reads w -> Just (k * 1024 :: Word64)
      _                          -> Nothing
    -- Bytes, alone on the first line, or the word @max@.
    plainNumber t = case words t of
      (w : _) | [(b, "")] <- reads w -> Just (b :: Word64)
      _                              -> Nothing

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
--
-- Anything this thread runs into, the checker's thread runs into too -- they
-- are reading one list -- so a 'PoolEvicted' raised here is swallowed and left
-- for the thread whose business it is to answer for it.  Reported here it would
-- be reported twice, and reported from a thread that decides nothing.
--
-- It is held to @window@ declarations in front, for the reason 'withPipeline'
-- holds its own backlog down: a declaration read and not yet walked is a
-- declaration's worth of terms that nothing can collect, and reading the whole
-- of @mathlib@ before checking any of it is how the live set came to be the
-- file rather than the work.  A window is all the overlap there is to have --
-- what it is hiding is the reading of a few thousand lines, not of a file --
-- and the walk never catches up with one this size.
prefetch :: Int -> IORef Int -> [a] -> IO ()
prefetch window at xs = () <$ forkIO (go 0 xs `catch` \PoolEvicted{} -> pure ())
  where
    go !_ []       = pure ()
    go !i (y : ys) = do
      -- Not every time round: the check is a read of someone else's cache line
      -- and the answer is almost always the same one.  Overshooting the window
      -- by a fraction of it is not worth avoiding.
      when (i `rem` 64 == 0) (hold i)
      y `seq` go (i + 1) ys

    hold i = do
      k <- readIORef at
      when (i - k > window) $ threadDelay 500 >> hold i

-- | Run @n@ threads on the obligations the walk hands them, keeping at most
-- @cap@ declarations waiting to be taken.
--
-- Pass one is the sequential part of a @-jN@ run and the obligations are the
-- parallel one, so running them after it is a queue behind a bottleneck: on
-- @std@ pass one is sixteen seconds of one thread while fifteen threads have
-- nothing to do, and the obligations are a hundred and thirteen seconds of work
-- that would fit inside it seven times over.  Handed over as pass one files
-- them, they mostly do fit.
--
-- The @cap@ is what this is really for.  An obligation holds the term it is
-- about and the environment it was admitted in, so an obligation not yet
-- discharged is a declaration's worth of heap that cannot be collected; and
-- pass one files them faster than @n@ threads can take them.  Left to run, the
-- backlog is the whole file -- on @mathlib@ several gigabytes of it, and the
-- largest single thing in the live set.  So the walk waits when the queue is
-- full.  There is no throughput in going faster than that: what the walk would
-- produce, nobody could take.
--
-- The room is given back when a thread /takes/ an obligation and not when it
-- finishes with it, and that distinction is the whole of the scheduling.  What
-- is held either way is bounded -- @cap@ waiting and one per thread in hand,
-- since a thread works on one at a time -- but charging for the work as well as
-- the queue lets a slow obligation stop the queue being refilled.  Obligations
-- are wildly uneven: @mathlib@ has one theorem that is most of its pass two, and
-- with the room charged to it as well, seven threads ran the queue dry and then
-- waited on the eighth.  Measured, that was 2.0 of 8 cores idle for the whole
-- run and @mathlib@ forty per cent slower, for no memory at all.
--
-- This decides nothing.  These are the same 'Obligation' values 'Done' hands
-- back, and forcing one is idempotent, so a thread here is doing the work
-- 'Front.Lower.discharge' would otherwise do later -- never work twice, and
-- never work that counts, since @discharge@ still reads every obligation in
-- file order and it is that reading which gives the verdict (SPEC.md §11.6).
-- For the same reason a thread that dies on one may simply be let die: the
-- obligation reverts to a thunk, and the reader forces it again and is told the
-- same thing on the thread whose business it is.
--
-- The @budget@ is the second bound, and it is on the work rather than on the
-- queue.  What the queue holds is small -- an obligation is a thunk -- and what
-- checking one costs is not: the memo tables a hard declaration builds are most
-- of the live set while it runs, and @n@ of those at once is @n@ times that.
-- Measured on @mathlib@ with a heap census, the live set is 3.3 GB and flat for
-- forty minutes and then climbs to 11.5 GB in the last three, 73% of it
-- application nodes: the file ends in a run of declarations that cost about a
-- gigabyte each, and eight at once is the whole of the difference between
-- fitting on a sixteen gigabyte machine and not.
--
-- What the budget cannot be is a gate on starting, which is what it was first
-- written as, and the census is why.  A thread that waits while the live set is
-- over the budget stops the /next/ obligation and not the eight already running,
-- and it is those eight that spend the memory: they are admitted together while
-- the live set is still 3.3 GB and grow past the budget on their way.  Measured,
-- the gate moved @mathlib@'s peak by three per cent between a 3 GB budget and a
-- 5 GB one -- both of them ten gigabytes, because both admitted eight.
--
-- So the budget governs how many run at once.  @allow@ starts at @n@ and moves
-- with the collector's reports: halved when a major collection finds more alive
-- than the budget, raised by one when it finds comfortably less.  Halving is
-- what makes it react inside a single burst rather than several -- the climb
-- above is three minutes long, which is a dozen major collections and plenty of
-- time -- and raising by one is what keeps it from giving the parallelism up for
-- a single spike.  It settles where the file needs it to: at a base of 3.3 GB
-- and a gigabyte apiece, a 5.3 GB budget holds two, and the run is
-- eight-threaded everywhere else.  Nobody has to say in advance how much
-- parallelism the file can afford, which is just as well, since it depends on
-- the file -- @std@ and @cslib@ never come near their budget and are never
-- throttled at all.
--
-- One thread is always admitted, since @allow@ never goes below one and the
-- wait is only entered when somebody else is working.  With everything else idle
-- there is nothing left for waiting to reclaim, so waiting would be waiting for
-- ever; and the figure being waited on comes from the collector, which needs
-- somebody to be allocating before it has anything new to say.  That is what
-- makes this an ordering on the threads and not a way to stop.
withPipeline :: Int -> Int -> Word64 -> (([Obligation] -> IO ()) -> IO a) -> IO a
withPipeline n cap budget body = do
  queue <- newChan
  room  <- newQSemN cap
  allow <- newIORef n
  busy  <- newIORef (0 :: Int)
  gone  <- newEmptyMVar
  hasStats <- getRTSStatsEnabled
  watch <- if budget == 0 || not hasStats
             then pure Nothing
             else do
               seen <- newIORef (0, 0)
               Just <$> forkIO
                 (forever (sample n budget allow seen >> threadDelay 20000))
  let admit :: IO ()
      admit | budget == 0 || not hasStats = pure ()
            | otherwise                   = wait
        where
          wait = do
            k <- readIORef busy
            a <- readIORef allow
            when (k > 0 && k >= a) (threadDelay 5000 >> wait)
  mapM_ (const (forkIO (worker queue room busy admit `finally` putMVar gone ())))
        [1 .. n]
  let submit obs = waitQSemN room 1 >> writeChan queue (Just obs)
      -- One end marker each, behind everything already written: a thread that
      -- takes one has seen all of them.  Then wait, because the caller reads
      -- the answers next and they are only answers once someone has worked them
      -- out.  Reached however @body@ ended, so nothing is left running.
      stop = do mapM_ (const (writeChan queue Nothing)) [1 .. n]
                mapM_ (const (takeMVar gone)) [1 .. n]
                mapM_ killThread watch
  body submit `finally` stop
  where
    worker queue room busy admit = loop
      where
        loop = readChan queue >>= \case
          Nothing  -> pure ()
          Just obs -> do
            signalQSemN room 1
            () <- admit
            atomicModifyIORef' busy (\k -> (k + 1, ()))
            evaluate (foldr (\ob r -> obCheck ob `seq` r) () obs)
              `catch` \(_ :: SomeException) -> pure ()
            atomicModifyIORef' busy (\k -> (k - 1, ()))
            loop

-- | One step of the controller: read what the last major collections found
-- alive, and move @allow@ towards the number of threads that figure can afford.
--
-- Only a major collection knows how much is alive; what a minor one reports is
-- what survived the youngest generation, which is a fraction of the answer and
-- would read as the pressure having gone.  But the details of the last
-- collection are no way to find the major ones -- with a nursery this size the
-- minor collections outnumber them by thousands, so a thread waking every twenty
-- milliseconds and asking what the last collection was almost always finds a
-- minor one and learns nothing.  The two running totals are the way: their
-- differences since the last look are the major collections that happened while
-- this thread was not looking and the bytes they found, however many that was
-- and whenever they were, and no collection is read twice or missed.
--
-- Halve and add one.  A control loop wants to come down faster than it goes up
-- when overshooting is what costs -- here it costs the run's memory, and going
-- back up costs only the time to notice -- and the two are not symmetric in
-- their evidence either: one collection over the budget is a fact about the
-- present, while a collection under it may be the pause before the next hard
-- declaration.  The floor is one thread and the ceiling is the @-jN@ asked for.
sample :: Int -> Word64 -> IORef Int -> IORef (Word64, Word64) -> IO ()
sample n budget allow seen = do
  s <- getRTSStats
  let majors = fromIntegral (major_gcs s)
      total  = cumulative_live_bytes s
  (majors0, total0) <- readIORef seen
  when (majors > majors0) $ do
    writeIORef seen (majors, total)
    -- The mean over the collections since the last look, which for the usual
    -- case of one collection is that collection.
    let live = (total - total0) `div` (majors - majors0)
    modifyIORef' allow $ \a ->
      if live > budget           then max 1 (a - max 1 (a `div` 2))
      else if live < easy budget then min n (a + 1)
      else a
  where
    -- Room to spare, and not merely under: a controller that raises the moment
    -- it is under the budget spends its time crossing it.
    easy b = b - b `div` 4

-- | Say something on stderr, if the run is one that reports.
remark :: Options -> String -> IO ()
remark o s = when (isJust (optProgress o)) $ hPutStrLn stderr ("[ " ++ s ++ " ]")

-- | Drive the trace to its verdict.
--
-- Without @--progress@ this is a plain fold and costs a clock read per
-- declaration at most; with it, every declaration is timed and the slow ones are
-- named.
-- The obligations of each declaration are handed to @submit@ as they go by --
-- which is where the run gets its parallelism, and where it gets its back
-- pressure, since 'withPipeline' makes this wait when the threads are behind --
-- and @at@ is left holding the number of declarations walked, which is what
-- 'prefetch' steers by.
walk :: Options -> ([Obligation] -> IO ()) -> IORef Int -> [Progress]
     -> IO (Either String (Env, [Obligation]))
walk o submit at ps0 = case optProgress o of
    Nothing  -> quiet (0 :: Int) ps0
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
      let loud !i (Starting mn : ps) = do
            t <- getMonotonicTime
            writeIORef cur (mn, t)
            loud i ps
          loud !i (Checked mn obs : ps) = do
            t       <- getMonotonicTime
            (_, s)  <- readIORef cur
            modifyIORef' n (+ 1)
            when (t - s >= cut) $ note (secs (t - s) ++ "  " ++ nameOf mn)
            step i obs
            loud (i + 1) ps
          loud !_ (Failed err : _) = do
            note "stopped:"
            getMonotonicTime >>= tally
            pure (Left err)
          loud !_ (Done env obs : _) = do
            getMonotonicTime >>= tally
            pure (Right (env, obs))
          loud !_ [] = pure (Left "internal error: export trace ended")
      r <- loud (0 :: Int) ps0
      killThread beat
      pure r
  where
    quiet !_ (Failed err   : _) = pure (Left err)
    quiet !_ (Done env obs : _) = pure (Right (env, obs))
    quiet !i (Starting _   : r) = quiet i r
    quiet !i (Checked _ obs: r) = step i obs >> quiet (i + 1) r
    quiet !_ []                 = pure (Left "internal error: export trace ended")

    -- Say where the walk has got to, and hand over what this declaration put
    -- off.  The order matters: 'prefetch' is let forward before 'submit' is
    -- allowed to block, so a walk that stalls on a busy pipeline is one the
    -- reader can be getting ahead of.
    step i obs = do
      writeIORef at (i + 1)
      case obs of
        [] -> pure ()
        _  -> submit obs

    note s = hPutStrLn stderr ("[ " ++ s ++ " ]")
    secs t = showFFloat (Just 2) t "s"
    nameOf = maybe "<block>" showName

    heartbeat :: Double
    heartbeat = 60
