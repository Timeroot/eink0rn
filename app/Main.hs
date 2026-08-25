-- | @eink0rn [OPTIONS] FILE.ndjson@ -- accept or reject an exported Lean
-- environment.
module Main (main) where

import qualified Data.ByteString.Char8 as B
import           Data.List             (isPrefixOf)
import           Front.Export          (parseExport)
import           Front.Lower           (checkExport, checkStdPins)
import           Kernel.Env            (AccelMode (..))
import           System.Environment    (getArgs, getProgName)
import           System.Exit           (ExitCode (..), exitFailure, exitSuccess,
                                        exitWith)
import           System.IO             (char8, hPutStrLn, hSetEncoding, stderr,
                                        stdout)

-- | How a failed @--pin-std@ audit is reported.
data PinMode = PinOff | PinWarn | PinError
  deriving Eq

data Options = Options
  { optAccel :: AccelMode
  , optPin   :: PinMode
  , optFile  :: Maybe String
  }

defaults :: Options
defaults = Options AccelCanonical PinOff Nothing

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
  , "  --pin-std=LEVEL    audit False, Eq, Iff, Nonempty, the quotient package"
  , "                     and the three axioms against their standard forms"
  , "      off              do not audit (default)"
  , "      warn             report mismatches on stderr, but accept"
  , "      error            reject the file on a mismatch"
  ]

parseArgs :: [String] -> Either String Options
parseArgs = foldl step (Right defaults)
  where
    step acc arg = acc >>= \o -> case arg of
      _ | arg `elem` ["-h", "--help"] -> Left ""
        | Just v <- stripFlag "--nat-accel=" arg -> (\m -> o { optAccel = m }) <$> accel v
        | Just v <- stripFlag "--pin-std="   arg -> (\m -> o { optPin   = m }) <$> pin v
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

main :: IO ()
main = do
  -- A 'Kernel.Name.Name' holds the bytes the export file held, undecoded: the
  -- kernel never looks inside one except to compare it, and a byte string
  -- compares the same either way.  Diagnostics have to put those bytes back on
  -- the wire unchanged, or a name like @α@ comes out re-encoded twice.  A
  -- byte-transparent handle is the whole fix; everything the checker writes
  -- itself is ASCII.
  mapM_ (`hSetEncoding` char8) [stdout, stderr]
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
  case parseExport input >>= checkExport (optAccel o) of
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
