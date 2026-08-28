{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE LambdaCase   #-}
-- Under @-jN@ the reader thread and pass one walk the same list, and where they
-- meet they meet on a thunk: the tail of that list, and the parse state behind
-- it.  GHC's default is to claim a thunk only once its evaluation is finished,
-- which is free but lets two threads that arrive together each do the whole
-- thing.  That is a fair bet when the thunk is small.  It is a bad one here,
-- because every thunk in this module stands for a stretch of the file, and pass
-- one is now fast enough to catch the reader up: on @std@ the two of them
-- between them read the file about one and a half times over, which showed up
-- as ten gigabytes of allocation that a @-j1@ run of the same binary did not
-- have.  Claiming the thunk on entry costs a write per thunk and settles it.
-- Only here, since only this module's thunks are shared across threads --
-- an obligation is checked by whichever thread took it and no other.
{-# OPTIONS_GHC -feager-blackholing #-}
-- | Reading a @lean4export@ NDJSON stream into core terms.
--
-- The file is a sequence of lines.  Most define one entry of a pool -- a name,
-- a level or an expression -- keyed by an integer given in the @in@ / @il@ /
-- @ie@ field; the rest are declarations.  Indices are sparse and need not be
-- monotonic, but a pool entry is always written before anything that mentions
-- it, so a single left-to-right pass suffices.  Index 0 is implicit: the
-- anonymous name and the level @0@.
--
-- **Every line is validated against the format, not merely mined for the
-- fields the kernel wants.**  A line carries exactly one tag saying what it is,
-- plus a pool index if it is a pool entry; the object under the tag has exactly
-- the fields the format gives it, with exactly the types and enumerations the
-- format gives them.  Anything else is a rejection, and the reason is that a
-- reader which skips what it does not recognise is choosing an interpretation
-- for a line nobody wrote.  Concretely: a @lam@ with no @binderInfo@, a @def@
-- with no @safety@, an @axiom@ with no @isUnsafe@ are all lines that a real
-- exporter cannot emit and that a lenient reader silently supplies a default
-- for -- and the default it supplies is the permissive one.
--
-- Two things are dropped here rather than in "Front.Lower", because they never
-- reach the core term language at all: binder annotations and @mdata@.  Both
-- are elaborator bookkeeping with no effect on typing or reduction.  They are
-- checked to be well-formed before they are dropped.
module Front.Export
  ( ExDecl (..)
  , ExInd (..)
  , ExCtor (..)
  , ExRec (..)
  , ExRule (..)
  , parseExport
  ) where

import qualified Data.ByteString.Char8  as B
import qualified Data.ByteString.Unsafe as BU
import           Data.Char              (isDigit)
import           Data.Word              (Word8)
import           Front.Json
import           Front.Pool
import           Kernel.Env             (Hint (..), QuotKind (..))
import           Kernel.Expr
import           Kernel.Level
import           Kernel.Name

-- | A declaration, with every index already resolved.  Fields the kernel has no
-- use for (@hints@, @all@) are validated and dropped; @isUnsafe@ and @safety@
-- are validated and /kept/, because they decide which fragment the declaration
-- joins (SPEC.md §12.7); @isRec@ and @isReflexive@ are kept, because the kernel
-- derives them itself and requires agreement.
data ExDecl
  = ExAxiom  !Bool !Name ![Name] !Expr
  | ExDef    !Bool !Name ![Name] !Expr !Expr !Hint
  | ExThm    !Name ![Name] !Expr !Expr
  | ExOpaque !Bool !Name ![Name] !Expr !Expr
  | ExQuot   !Name ![Name] !Expr !QuotKind
  | ExInduct ![ExInd] ![ExCtor] ![ExRec]
  deriving (Show)

data ExInd = ExInd
  { exiName        :: !Name
  , exiLevels      :: ![Name]
  , exiType        :: !Expr
  , exiNumParams   :: !Int
  , exiNumIndices  :: !Int
  , exiAll         :: ![Name]
  , exiCtors       :: ![Name]
  , exiNumNested   :: !Int
  , exiIsRec       :: !Bool
  , exiIsReflexive :: !Bool
  , exiIsUnsafe    :: !Bool
  } deriving (Show)

data ExCtor = ExCtor
  { excName      :: !Name
  , excLevels    :: ![Name]
  , excType      :: !Expr
  , excInduct    :: !Name
  , excIdx       :: !Int
  , excNumParams :: !Int
  , excNumFields :: !Int
  , excIsUnsafe  :: !Bool
  } deriving (Show)

data ExRec = ExRec
  { exrName       :: !Name
  , exrLevels     :: ![Name]
  , exrType       :: !Expr
  , exrAll        :: ![Name]
  , exrNumParams  :: !Int
  , exrNumIndices :: !Int
  , exrNumMotives :: !Int
  , exrNumMinors  :: !Int
  , exrRules      :: ![ExRule]
  , exrK          :: !Bool
  , exrIsUnsafe   :: !Bool
  } deriving (Show)

data ExRule = ExRule
  { exuCtor      :: !Name
  , exuNumFields :: !Int
  , exuRhs       :: !Expr
  } deriving (Show)

-- The pools --------------------------------------------------------------------

data Pools = Pools
  { pNames  :: !(Pool Name)
  , pLevels :: !(Pool Level)
  , pExprs  :: !(Pool Expr)
  }

emptyPools :: Pools
emptyPools = Pools (poolPush 0 Anon emptyPool) (poolPush 0 LZero emptyPool) emptyPool

-- | Read a whole export.  Declarations come back in stream order.
--
-- Lazily: reading resumes where it left off when the next declaration is asked
-- for, and a line is looked at only once something wants what is past it.  Which
-- is what lets a caller with a core to spare read the file and check it at the
-- same time -- see @Main.prefetch@ -- and it is why a bad line is an element of
-- the list rather than the whole of it.  A 'Left' is the last element there is:
-- the pools are built left to right, so nothing after a line that could not be
-- read can be trusted to mean what it says.
--
-- The order in which problems are reported is therefore file order throughout: a
-- declaration that does not typecheck is reported ahead of a malformed line
-- below it, where reading the file first would have reported the malformed line.
parseExport :: B.ByteString -> [Either String ExDecl]
parseExport input = go (1 :: Int) emptyPools 0
  where
    len = B.length input

    -- Lines are found rather than made: 'fastLine' matches straight into the
    -- file at an offset and says where the next line starts, so the nine lines
    -- in ten it recognises never become a 'B.ByteString' of their own.  Only the
    -- rest are cut out, for 'step' to read as before.
    --
    -- The line number is wanted only by the error branches, so nothing else
    -- forces it: without the bang a file with ten million lines in it builds ten
    -- million additions before anything asks what line this is.
    go !ln ps !off
      | off >= len = []
      | otherwise  = case fastLine ps input off of
          FastOk ps' nxt -> go (ln + 1) ps' nxt
          FastErr err    -> [Left (at ln err)]
          NotFast        -> slow ln ps (B.takeWhile (/= '\n') (B.drop off input))
      where
        -- Past the newline, or -- on a last line that has none -- one past the
        -- end, which the guard above reads as the end.  A file that /does/ end
        -- in a newline leaves @off == len@, and that is the empty last line
        -- 'B.lines' also declines to produce.
        slow ln' ps' l
          | B.null (B.dropWhile (`elem` " \t\r") l) = go (ln' + 1) ps' nxt
          | otherwise = case step ps' l of
              Left err              -> [Left (at ln' err)]
              Right (ps'', Nothing) -> go (ln' + 1) ps'' nxt
              Right (ps'', Just d)  -> Right d : go (ln' + 1) ps'' nxt
          where nxt = off + B.length l + 1

    at ln err = "line " ++ show ln ++ ": " ++ err

-- The shapes that are most of a file ----------------------------------------------
--
-- An export is overwhelmingly applications, binders, names and constants, and
-- each kind is written in exactly one shape, character for character:
--
-- > {"app":{"arg":N,"fn":M},"ie":K}
-- > {"ie":K,"lam":{"binderInfo":"B","body":N,"name":M,"type":T}}
-- > {"forallE":{"binderInfo":"B","body":N,"name":M,"type":T},"ie":K}
-- > {"in":K,"str":{"pre":P,"str":"S"}}
-- > {"in":K,"num":{"i":I,"pre":P}}
-- > {"const":{"name":N,"us":[U,...]},"ie":K}
--
-- In @std@ those account for 9,897,300 of 10,023,185 lines, and across all four
-- corpora there is not one line of any of these kinds that differs from its
-- shape by a byte.  Building a 'Json' value for each of them -- a list of pairs,
-- a boxed 'Integer' per index, a 'String' per key, all of it dead the moment the
-- pool lookups are done -- is most of what reading an export costs.
--
-- The first three are nine lines in ten on their own.  The other three are seven
-- of every eight that remain, which is worth having because the general reader
-- is some twenty times the cost of a match: names and constants are 625,000
-- lines of @std@ and were about the same share of the reader's time as the nine
-- million lines above them.  Adding them took a single-threaded pass one over
-- @std@ from 13.8 to 12.5 seconds of CPU and dropped 1.1 GB of the 8.5 GB it
-- allocated; what is left for 'step' is 126,000 lines, one and a quarter per
-- cent, and most of that is @thm@ and @def@ headers.
--
-- What makes reading them this way safe is that it is a match and not a parse.
-- The literal stretches are compared byte for byte and every number must be a
-- run of one to eighteen digits; a space, a reordered key, a sign, an extra
-- field, a trailing byte -- anything at all that is not the exact shape returns
-- 'Nothing', and the line goes to 'step', which decides the format as before.
-- So this cannot admit a line the general reader rejects, only skip the work of
-- agreeing with it.  For the same reason the pool lookups are made in the order
-- 'readExpr' makes them, so that a line with two bad indices is still reported
-- against the same one.
--
-- 'NotFast' is "not one of these shapes"; 'FastErr' is "one of them, and an
-- index in it names a pool entry that does not exist".
--
-- The matching is done on the file itself, at an offset, and never on a line cut
-- out of it: a position is an 'Int', @-1@ says the shape did not match there, and
-- a matcher handed @-1@ passes it on.  So the chains below read as the shape they
-- match and allocate nothing at all while they are deciding -- where the same
-- three functions written over 'B.ByteString' slices allocated some four hundred
-- bytes a line, on ten million lines, to say what a dozen byte comparisons say.

-- | Where a fast line got to: the pools it leaves behind, and the offset the
-- next line starts at.
data Fast = NotFast | FastErr String | FastOk !Pools !Int

-- | Try the shapes, the one that could match first.
--
-- @{\"a@, @{\"c@, @{\"f@, @{\"i@: the openings are told apart by the third byte
-- and, where that is not enough, the fourth -- @{\"ie@ against @{\"in@ -- so a
-- line with something else there matches none of them and a line with one of
-- them can match only the one.  This is a filter and not a decision -- whichever
-- matcher is picked still matches its whole opening, those bytes included, and
-- still returns 'NotFast' if the rest of the line is not the shape.  It is here
-- because otherwise every @forallE@ line, and there are three million of them
-- in @std@, is walked twice over by matchers that gave up at the third byte.
--
-- @{\"inductive@ also begins @{\"in@, and is left to 'nameLine' to decline at
-- the colon that is not where @{\"in\":@ has one.  There are nine hundred of
-- them in @std@ against half a million names.
fastLine :: Pools -> B.ByteString -> Int -> Fast
fastLine ps s i
  | i + 4 > B.length s = NotFast
  | otherwise = case B.index s (i + 2) of
      'a' -> appLine ps s i
      'f' -> allLine ps s i
      'c' -> constLine ps s i
      'i' -> case B.index s (i + 3) of
               'e' -> lamLine ps s i
               'n' -> nameLine ps s i
               _   -> NotFast
      _   -> NotFast

-- | @{"app":{"arg":N,"fn":M},"ie":K}@.
appLine :: Pools -> B.ByteString -> Int -> Fast
appLine ps s i0 =
  case nat s (lit appOpen s i0) of { Cur i1 a ->
  case nat s (lit appFn   s i1) of { Cur i2 f ->
  case nat s (lit appIe   s i2) of { Cur i3 k ->
  case eol s (lit close   s i3) of
    nxt | nxt < 0   -> NotFast
        | otherwise -> case exprIx ps f of
            Left err -> FastErr err
            Right fn -> case exprIx ps a of
              Left err  -> FastErr err
              Right arg -> FastOk (fileExpr k (App fn arg) ps) nxt }}}

-- | @{"ie":K,"lam":{"binderInfo":"B","body":N,"name":M,"type":T}}@.
lamLine :: Pools -> B.ByteString -> Int -> Fast
lamLine ps s i0 =
  case nat s (lit lamOpen s i0)      of { Cur i1 k  ->
  case nat s (binderInfoLit s
               (lit lamMid s i1))    of { Cur i2 b  ->
  case nat s (lit nameKey s i2)      of { Cur i3 nm ->
  case nat s (lit typeKey s i3)      of { Cur i4 t  ->
  case eol s (lit lamEnd  s i4) of
    nxt | nxt < 0   -> NotFast
        | otherwise -> binderAt ps Lam k nm t b nxt }}}}

-- | @{"forallE":{"binderInfo":"B","body":N,"name":M,"type":T},"ie":K}@.
allLine :: Pools -> B.ByteString -> Int -> Fast
allLine ps s i0 =
  case nat s (binderInfoLit s
               (lit allOpen s i0))   of { Cur i1 b  ->
  case nat s (lit nameKey s i1)      of { Cur i2 nm ->
  case nat s (lit typeKey s i2)      of { Cur i3 t  ->
  case nat s (lit allMid  s i3)      of { Cur i4 k  ->
  case eol s (lit close   s i4) of
    nxt | nxt < 0   -> NotFast
        | otherwise -> binderAt ps Pi k nm t b nxt }}}}

-- | File a binder, resolving its three indices in the order 'readExpr' does.
binderAt :: Pools -> (Binder -> Expr -> Expr -> Expr)
         -> Int -> Int -> Int -> Int -> Int -> Fast
binderAt ps con k nm t b nxt = case poolAt (pNames ps) nm of
  Nothing -> FastErr ("undefined name index " ++ show nm)
  Just n' -> case exprIx ps t of
    Left err -> FastErr err
    Right ty -> case exprIx ps b of
      Left err   -> FastErr err
      Right body -> FastOk (fileExpr k (con (Binder n') ty body) ps) nxt

-- | @{"in":K,"str":{"pre":P,"str":"S"}}@ and @{"in":K,"num":{"i":I,"pre":P}}@.
--
-- The two are told apart by the byte after @,"@, which is the only place they
-- can differ: the exporter writes a record's fields in alphabetical order, so a
-- @str@ name has its prefix first and a @num@ name has its numeral first.
nameLine :: Pools -> B.ByteString -> Int -> Fast
nameLine ps s i0 = case nat s (lit inOpen s i0) of
  Cur i1 k -> case nat s (lit strOpen s i1) of
    -- @{"str":{"pre":P,"str":"S"}}@
    Cur i2 p | i2 >= 0 -> case plainStr s (lit strMid s i2) of
      Slice i3 sv -> case eol s (lit nameEnd s i3) of
        nxt | nxt < 0   -> NotFast
            | otherwise -> fileName ps k nxt p (`mkStr` sv)
    -- @{"num":{"i":I,"pre":P}}@
    _ -> case nat s (lit numOpen s i1) of { Cur i2 v ->
         case nat s (lit numPre s i2) of { Cur i3 p ->
         case eol s (lit nameEnd s i3) of
           nxt | nxt < 0   -> NotFast
               | otherwise -> fileName ps k nxt p (`mkNum` toInteger v) }}

-- | File a name whose prefix is the pool entry @p@.  The prefix is the only
-- index a name line has to resolve, and 'readName' resolves it before it looks
-- at anything else, so there is only one error this can report.
fileName :: Pools -> Int -> Int -> Int -> (Name -> Name) -> Fast
fileName ps k nxt p mk = case poolAt (pNames ps) p of
  Nothing  -> FastErr ("undefined name index " ++ show p)
  Just pre -> FastOk (ps { pNames = poolPush k (mk pre) (pNames ps) }) nxt
{-# INLINE fileName #-}

-- | @{"const":{"name":N,"us":[U,...]},"ie":K}@.
--
-- The universe list is read as indices and resolved only once the whole line
-- has matched, so that a line which is this shape as far as the list and then
-- is not still reaches 'step' and is reported the way 'step' reports it.  The
-- resolution order is 'readExpr''s: the name, and then the universes left to
-- right.
constLine :: Pools -> B.ByteString -> Int -> Fast
constLine ps s i0 =
  case nat s (lit constOpen s i0) of { Cur i1 nm ->
  case natList s (lit constUs s i1) of { Nats i2 us ->
  case nat s (lit constIe s i2) of { Cur i3 k ->
  case eol s (lit close s i3) of
    nxt | nxt < 0   -> NotFast
        | otherwise -> case poolAt (pNames ps) nm of
            Nothing -> FastErr ("undefined name index " ++ show nm)
            Just n' -> case levelIxs ps us of
              Left err -> FastErr err
              Right ls -> FastOk (fileExpr k (Const n' ls) ps) nxt }}}

levelIxs :: Pools -> [Int] -> Either String [Level]
levelIxs ps = traverse one
  where
    one u = maybe (Left ("undefined level index " ++ show u)) Right
                  (poolAt (pLevels ps) u)

exprIx :: Pools -> Int -> Either String Expr
exprIx ps i = maybe (Left ("undefined expression index " ++ show i)) Right
                    (poolAt (pExprs ps) i)

fileExpr :: Int -> Expr -> Pools -> Pools
fileExpr k e ps = ps { pExprs = poolPush k e (pExprs ps) }

-- | The byte at a position inside the file.
--
-- Every use below is guarded, on the line above it, by a comparison of the
-- position against the length -- 'lit' checks its whole span before it starts,
-- the rest check each read -- so the check 'B.index' would make again is
-- dropped.  These run some four hundred million times over an export of @std@,
-- which is the only reason to care.
byteAt :: B.ByteString -> Int -> Word8
byteAt = BU.unsafeIndex
{-# INLINE byteAt #-}

-- | The bytes the matchers test for by hand, rather than through a literal.
wQuote, wBackslash, wNewline, wComma, wRBracket :: Word8
wQuote     = 34
wBackslash = 92
wNewline   = 10
wComma     = 44
wRBracket  = 93

-- | Match a literal at a position, and say where it ends.
lit :: B.ByteString -> B.ByteString -> Int -> Int
lit p s i
  | i < 0 || i + n > B.length s = -1
  | otherwise                   = go 0
  where
    n = B.length p
    go !j | j == n                             = i + n
          | byteAt s (i + j) == byteAt p j     = go (j + 1)
          | otherwise                          = -1

-- | The end of the line, and where the next one starts.
--
-- A last line with no newline after it ends at the end of the file, and the
-- offset one past it is what the loop reads as "nothing left".
eol :: B.ByteString -> Int -> Int
eol s i
  | i < 0 || i > B.length s = -1
  | i == B.length s         = i
  | byteAt s i == wNewline  = i + 1
  | otherwise               = -1

-- | Where a string matcher got to, and the bytes it read.
data Slice = Slice !Int !B.ByteString

-- | A JSON string with nothing in it that needs decoding, from just past its
-- opening quote.
--
-- 'Front.Json.pString' slices such a string straight out of the line, and this
-- returns those same bytes.  A backslash is an escape, which is that function's
-- business and not this one's; a newline means the string is not closed on this
-- line at all.  Either way the line goes to the general reader.
plainStr :: B.ByteString -> Int -> Slice
plainStr s i
  | i < 0     = Slice (-1) B.empty
  | otherwise = go i
  where
    n = B.length s
    go !j
      | j >= n                           = Slice (-1) B.empty
      | w == wQuote                      = Slice (j + 1) (B.take (j - i) (B.drop i s))
      | w == wBackslash || w == wNewline = Slice (-1) B.empty
      | otherwise                        = go (j + 1)
      where w = byteAt s j

-- | Where a list matcher got to, and the numbers in it.
data Nats = Nats !Int [Int]

-- | @[N,N,...]@ or @[]@, from just past the opening bracket.
natList :: B.ByteString -> Int -> Nats
natList s i
  | i < 0 || i >= B.length s = bad
  | byteAt s i == wRBracket  = Nats (i + 1) []
  | otherwise                = go i
  where
    bad = Nats (-1) []
    n   = B.length s
    go j = case nat s j of
      Cur (-1) _ -> bad
      Cur j' u
        | j' >= n                  -> bad
        | byteAt s j' == wComma    -> case go (j' + 1) of
            Nats (-1) _  -> bad
            Nats j'' us  -> Nats j'' (u : us)
        | byteAt s j' == wRBracket -> Nats (j' + 1) [u]
        | otherwise                -> bad

-- | Where a matcher got to, and the number it read there.
data Cur = Cur !Int !Int

-- | A run of digits, as a number.
--
-- One to eighteen of them -- eighteen being as many as cannot overflow an 'Int'.
-- Nineteen is not "read the first eighteen": a number too large for the index it
-- is going to be is left to 'step', which checks the range properly and says so,
-- rather than being wrapped into an index that happens to exist.  Nor is a sign
-- taken, which is why this is not 'B.readInt'.
--
-- @w - 48 <= 9@ is @'0' <= c && c <= '9'@ written as one comparison: 'Word8'
-- subtraction wraps, so a byte below @'0'@ comes out somewhere above 200.
nat :: B.ByteString -> Int -> Cur
nat s i
  | i < 0     = Cur (-1) 0
  | otherwise = go i 0 0
  where
    n = B.length s
    go !j !d !v
      | j < n, w <- byteAt s j, w - 48 <= 9 =
          if d == (18 :: Int) then Cur (-1) 0
                              else go (j + 1) (d + 1) (v * 10 + fromIntegral w - 48)
      | d == 0    = Cur (-1) 0
      | otherwise = Cur j v

-- | One of the four binder annotations, followed by the key that comes after it.
--
-- The annotation itself is discarded, exactly as 'binderInfoOf' discards it; it
-- is matched only because a line carrying one this reader does not know is a
-- line written against a format it does not know.
binderInfoLit :: B.ByteString -> Int -> Int
binderInfoLit s i
  | i < 0     = -1
  | otherwise = go binderInfoLits
  where
    go []       = -1
    go (p : pr) = case lit p s i of
      -1 -> go pr
      j  -> j

-- | The literal stretches, packed once at the top level rather than at each of
-- ten million comparisons.
appOpen, appFn, appIe, lamOpen, lamMid, lamEnd, allOpen, allMid,
  inOpen, strOpen, strMid, numOpen, numPre, nameEnd,
  constOpen, constUs, constIe,
  nameKey, typeKey, close :: B.ByteString
appOpen   = B.pack "{\"app\":{\"arg\":"
appFn     = B.pack ",\"fn\":"
appIe     = B.pack "},\"ie\":"
lamOpen   = B.pack "{\"ie\":"
lamMid    = B.pack ",\"lam\":{\"binderInfo\":\""
lamEnd    = B.pack "}}"
allOpen   = B.pack "{\"forallE\":{\"binderInfo\":\""
allMid    = B.pack "},\"ie\":"
inOpen    = B.pack "{\"in\":"
strOpen   = B.pack ",\"str\":{\"pre\":"
strMid    = B.pack ",\"str\":\""
numOpen   = B.pack ",\"num\":{\"i\":"
numPre    = B.pack ",\"pre\":"
nameEnd   = B.pack "}}"
constOpen = B.pack "{\"const\":{\"name\":"
constUs   = B.pack ",\"us\":["
constIe   = B.pack "},\"ie\":"
nameKey   = B.pack ",\"name\":"
typeKey   = B.pack ",\"type\":"
close     = B.pack "}"

binderInfoLits :: [B.ByteString]
binderInfoLits = map B.pack
  [ "default\",\"body\":", "implicit\",\"body\":"
  , "instImplicit\",\"body\":", "strictImplicit\",\"body\":" ]

-- | The keys that say where a pool entry is filed, as opposed to what it is.
poolKeys :: [String]
poolKeys = ["in", "il", "ie"]

-- | Process one line: either it extends a pool or it yields a declaration.
--
-- A line says what it is with exactly one tag.  Two tags is not a line with a
-- spare field, it is two lines written as one, and there is no reading of it
-- that is obviously the intended one.
step :: Pools -> B.ByteString -> Either String (Pools, Maybe ExDecl)
step ps line = do
  v <- parseJsonLine line
  o <- asObject v
  case tagsOf poolKeys o of
    [t] -> entry ps t v
    []  -> Left "line has no tag saying what it is"
    ts  -> Left ("line carries more than one tag: "
                 ++ unwords (map show ts))

entry :: Pools -> String -> Json -> Either String (Pools, Maybe ExDecl)
entry ps t v
  | t `elem` ["str", "num"] = pool "in" pNames (\m -> ps { pNames = m })
                                   (readName ps t)
  | t `elem` ["succ", "max", "imax", "param"] =
                              pool "il" pLevels (\m -> ps { pLevels = m })
                                   (readLevel ps t)
  | t `elem` exprTags       = pool "ie" pExprs (\m -> ps { pExprs = m })
                                   (readExpr ps t)
  -- The metadata header is the one line whose shape the kernel has no stake in:
  -- it names the exporter and the format version and says nothing about the
  -- environment.  Real exports vary in which sub-objects they include, so it is
  -- checked only to be a lone well-formed @meta@ line.
  | t == "meta"             = record ["meta"] v >> pure (ps, Nothing)
  | t `notElem` declTags    = Left ("unrecognised tag " ++ show t)
  -- A declaration line is the tag and nothing else: no pool index, since a
  -- declaration is not something anything else refers to by number.
  | otherwise               = do f <- record [t] v
                                 d <- readDecl ps t =<< field f t
                                 pure (ps, Just d)
  where
    pool key get put rd = do
      f <- record [t, key] v
      k <- natOf =<< field f key
      x <- rd =<< field f t
      pure (put (poolPush k x (get ps)), Nothing)

exprTags :: [String]
exprTags =
  [ "bvar", "sort", "const", "app", "lam", "forallE", "letE", "proj"
  , "natVal", "strVal", "mdata" ]

declTags :: [String]
declTags = ["axiom", "def", "thm", "opaque", "quot", "inductive"]

-- | A natural that has to fit in an 'Int'.  Every count and index a real export
-- contains does so by an enormous margin; one that does not is either a forged
-- file or a file this checker could not finish anyway, and in both cases saying
-- so beats wrapping around into a small positive number.
natOf :: Json -> Either String Int
natOf j = do
  n <- asNat j
  if n <= toInteger (maxBound :: Int)
    then Right (fromInteger n)
    else Left ("number out of range: " ++ show n)

-- Pool lookups ------------------------------------------------------------------

nameAt :: Pools -> Json -> Either String Name
nameAt ps j = do
  i <- natOf j
  maybe (Left ("undefined name index " ++ show i)) Right (poolAt (pNames ps) i)

levelAt :: Pools -> Json -> Either String Level
levelAt ps j = do
  i <- natOf j
  maybe (Left ("undefined level index " ++ show i)) Right (poolAt (pLevels ps) i)

exprAt :: Pools -> Json -> Either String Expr
exprAt ps j = do
  i <- natOf j
  maybe (Left ("undefined expression index " ++ show i)) Right (poolAt (pExprs ps) i)

namesAt :: Pools -> Json -> Either String [Name]
namesAt ps j = asArray j >>= mapM (nameAt ps)

levelList :: Pools -> Json -> Either String [Level]
levelList ps j = asArray j >>= mapM (levelAt ps)

-- Readers -----------------------------------------------------------------------

readName :: Pools -> String -> Json -> Either String Name
readName ps t v = case t of
  "str" -> do
    f <- record ["pre", "str"] v
    mkStr <$> (nameAt ps =<< field f "pre") <*> (asString =<< field f "str")
  _     -> do
    f <- record ["pre", "i"] v
    mkNum <$> (nameAt ps =<< field f "pre") <*> (asNat =<< field f "i")

readLevel :: Pools -> String -> Json -> Either String Level
readLevel ps t v = case t of
  "succ"  -> mkSucc <$> levelAt ps v
  "max"   -> binary mkMax
  "imax"  -> binary mkIMax
  _       -> LParam <$> nameAt ps v
  where
    binary f = asArray v >>= \case
      [x, y] -> f <$> levelAt ps x <*> levelAt ps y
      other  -> Left ("expected a pair of level indices, got "
                      ++ show (length other) ++ " of them")

readExpr :: Pools -> String -> Json -> Either String Expr
readExpr ps t v = case t of
  "bvar"    -> BVar <$> natOf v
  "sort"    -> Sort <$> levelAt ps v
  "const"   -> do
    f <- record ["name", "us"] v
    Const <$> (nameAt ps =<< field f "name")
          <*> (levelList ps =<< field f "us")
  "app"     -> do
    f <- record ["fn", "arg"] v
    App <$> (exprAt ps =<< field f "fn") <*> (exprAt ps =<< field f "arg")
  "lam"     -> binder Lam
  "forallE" -> binder Pi
  "letE"    -> do
    f <- record ["name", "type", "value", "body", "nondep"] v
    _ <- asBool =<< field f "nondep"      -- an elaboration hint; erased
    Let <$> (Binder <$> (nameAt ps =<< field f "name"))
        <*> (exprAt ps =<< field f "type")
        <*> (exprAt ps =<< field f "value")
        <*> (exprAt ps =<< field f "body")
  "proj"    -> do
    f <- record ["typeName", "idx", "struct"] v
    Proj <$> (nameAt ps =<< field f "typeName")
         <*> (natOf =<< field f "idx")
         <*> (exprAt ps =<< field f "struct")
  "natVal"  -> do
    s <- asString v
    if not (B.null s) && B.all isDigit s
      then Right (NatLit (B.foldl' (\a c -> a * 10 + toInteger (fromEnum c - 48)) 0 s))
      else Left ("malformed natVal " ++ show (B.unpack s))
  "strVal"  -> StrLit <$> asString v
  _         -> do
    f <- record ["expr", "data"] v
    _ <- asObject =<< field f "data"      -- annotations are erased
    exprAt ps =<< field f "expr"
  where
    binder con = do
      f <- record ["name", "type", "body", "binderInfo"] v
      _ <- binderInfoOf =<< field f "binderInfo"
      con <$> (Binder <$> (nameAt ps =<< field f "name"))
          <*> (exprAt ps =<< field f "type")
          <*> (exprAt ps =<< field f "body")

-- | Checked, then discarded.  The annotation tells the elaborator how to fill
-- an argument in and has no effect on typing or reduction, but an unrecognised
-- one means the file was written against a format this reader does not know,
-- and the honest answer to that is not to guess.
binderInfoOf :: Json -> Either String ()
binderInfoOf = enumOf "binderInfo"
  [("default", ()), ("implicit", ()), ("strictImplicit", ()), ("instImplicit", ())]

-- | @enumOf what alts j@: @j@ is one of the strings in @alts@.
enumOf :: String -> [(String, a)] -> Json -> Either String a
enumOf what alts j = do
  s <- asString j
  case lookup (B.unpack s) alts of
    Just a  -> Right a
    Nothing -> Left ("unknown " ++ what ++ " " ++ show (B.unpack s)
                     ++ "; expected one of " ++ unwords (map (show . fst) alts))

-- Safety --------------------------------------------------------------------------

-- | Is this declaration exempt from termination checking?
--
-- @unsafe def loop : False := loop@ is a well-formed input to the elaborator,
-- and a proof of @False@ to anything that reads its type and ignores the flag.
-- The flag therefore has to reach the checker rather than be validated and
-- dropped: it decides whether the declaration joins the theory of §5 or the
-- quarantined fragment of SPEC.md §12.7, and those two answers differ.
--
-- Two spellings, one meaning.  @def@ carries a three-valued @safety@; every
-- other kind carries a boolean @isUnsafe@.  @partial@ is @unsafe@ with a nicer
-- surface syntax -- the elaborator accepts a non-terminating body either way --
-- so both map to the same answer here.
--
-- Every declaration in all 186 arena exports is safe, so nothing in the corpus
-- takes the other branch.
readIsUnsafe :: Json -> Either String Bool
readIsUnsafe = asBool

readSafety :: Json -> Either String Bool
readSafety = enumOf "safety"
  [("safe", False), ("unsafe", True), ("partial", True)]

-- | @hints@ is scheduling advice for the unfolder.  It is the only field of the
-- export the kernel both keeps and never checks; see 'Hint' for why that costs
-- nothing.
readHints :: Json -> Either String Hint
readHints j = case j of
  JStr _ -> enumOf "hints" [("opaque", HOpaque), ("abbrev", HAbbrev)] j
  JObj _ -> do f <- record ["regular"] j
               n <- natOf =<< field f "regular"
               pure (HRegular n)
  _      -> Left "hints must be \"opaque\", \"abbrev\", or {\"regular\": n}"

-- Declarations --------------------------------------------------------------------

readDecl :: Pools -> String -> Json -> Either String ExDecl
readDecl ps t v = case t of
  "axiom" -> do
    f <- record ["name", "levelParams", "type", "isUnsafe"] v
    u <- readIsUnsafe =<< field f "isUnsafe"
    ExAxiom u <$> nm f <*> lps f <*> ty f
  "def" -> do
    f <- record ["name", "levelParams", "type", "value", "hints", "safety", "all"] v
    u <- readSafety =<< field f "safety"
    h <- readHints  =<< field f "hints"
    _ <- namesAt ps =<< field f "all"
    ExDef u <$> nm f <*> lps f <*> ty f <*> val f <*> pure h
  "thm" -> do
    f <- record ["name", "levelParams", "type", "value", "all"] v
    _ <- namesAt ps =<< field f "all"
    ExThm <$> nm f <*> lps f <*> ty f <*> val f
  "opaque" -> do
    f <- record ["name", "levelParams", "type", "value", "isUnsafe", "all"] v
    u <- readIsUnsafe =<< field f "isUnsafe"
    _ <- namesAt ps =<< field f "all"
    ExOpaque u <$> nm f <*> lps f <*> ty f <*> val f
  "quot" -> do
    f  <- record ["name", "levelParams", "type", "kind"] v
    qk <- enumOf "quotient kind"
            [("type", QType), ("ctor", QCtor), ("lift", QLift), ("ind", QInd)]
            =<< field f "kind"
    ExQuot <$> nm f <*> lps f <*> ty f <*> pure qk
  "inductive" -> do
    f  <- record ["types", "ctors", "recs"] v
    ts <- mapM (readInd ps)  =<< asArray =<< field f "types"
    cs <- mapM (readCtor ps) =<< asArray =<< field f "ctors"
    rs <- mapM (readRec ps)  =<< asArray =<< field f "recs"
    pure (ExInduct ts cs rs)
  _ -> Left ("unrecognised declaration tag " ++ show t)
  where
    nm  f = nameAt ps =<< field f "name"
    lps f = namesAt ps =<< field f "levelParams"
    ty  f = exprAt ps =<< field f "type"
    val f = exprAt ps =<< field f "value"

readInd :: Pools -> Json -> Either String ExInd
readInd ps v = do
  f <- record [ "name", "levelParams", "type", "numParams", "numIndices"
              , "all", "ctors", "numNested", "isRec", "isUnsafe", "isReflexive" ] v
  ExInd <$> (nameAt ps =<< field f "name")
        <*> (namesAt ps =<< field f "levelParams")
        <*> (exprAt ps =<< field f "type")
        <*> (natOf =<< field f "numParams")
        <*> (natOf =<< field f "numIndices")
        <*> (namesAt ps =<< field f "all")
        <*> (namesAt ps =<< field f "ctors")
        <*> (natOf =<< field f "numNested")
        <*> (asBool =<< field f "isRec")
        <*> (asBool =<< field f "isReflexive")
        <*> (readIsUnsafe =<< field f "isUnsafe")

readCtor :: Pools -> Json -> Either String ExCtor
readCtor ps v = do
  f <- record [ "name", "levelParams", "type", "induct", "cidx"
              , "numParams", "numFields", "isUnsafe" ] v
  ExCtor <$> (nameAt ps =<< field f "name")
         <*> (namesAt ps =<< field f "levelParams")
         <*> (exprAt ps =<< field f "type")
         <*> (nameAt ps =<< field f "induct")
         <*> (natOf =<< field f "cidx")
         <*> (natOf =<< field f "numParams")
         <*> (natOf =<< field f "numFields")
         <*> (readIsUnsafe =<< field f "isUnsafe")

readRec :: Pools -> Json -> Either String ExRec
readRec ps v = do
  f <- record [ "name", "levelParams", "type", "all", "numParams", "numIndices"
              , "numMotives", "numMinors", "rules", "k", "isUnsafe" ] v
  ExRec <$> (nameAt ps =<< field f "name")
        <*> (namesAt ps =<< field f "levelParams")
        <*> (exprAt ps =<< field f "type")
        <*> (namesAt ps =<< field f "all")
        <*> (natOf =<< field f "numParams")
        <*> (natOf =<< field f "numIndices")
        <*> (natOf =<< field f "numMotives")
        <*> (natOf =<< field f "numMinors")
        <*> (mapM (readRule ps) =<< asArray =<< field f "rules")
        <*> (asBool =<< field f "k")
        <*> (readIsUnsafe =<< field f "isUnsafe")

readRule :: Pools -> Json -> Either String ExRule
readRule ps v = do
  f <- record ["ctor", "nfields", "rhs"] v
  ExRule <$> (nameAt ps =<< field f "ctor")
         <*> (natOf =<< field f "nfields")
         <*> (exprAt ps =<< field f "rhs")
