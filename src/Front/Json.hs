{-# LANGUAGE BangPatterns #-}
-- | A minimal JSON reader, just enough for the lean4export NDJSON format.
--
-- Deliberately dependency-free: the whole point of this checker is that the
-- trusted path is small enough to read end to end.
module Front.Json
  ( Json (..)
  , parseJsonLine
  , record
  , field
  , optField
  , asInt
  , asNat
  , asString
  , asBool
  , asArray
  , asObject
  , tagsOf
  ) where

import qualified Data.ByteString.Char8 as B
import           Data.Bits             (shiftL, (.&.), (.|.))
import           Data.Char             (chr, digitToInt, isDigit, isHexDigit)
import           Data.List             (intercalate, nub)
import           Data.Word             (Word32)

data Json
  = JNull
  | JBool !Bool
  | JInt !Integer            -- ^ every number in this format is an integer
  | JStr !B.ByteString       -- ^ already unescaped, UTF-8 encoded
  | JArr [Json]
  | JObj [(B.ByteString, Json)]
  deriving (Eq, Show)

-- | Parse exactly one JSON value, which must consume the whole line.
parseJsonLine :: B.ByteString -> Either String Json
parseJsonLine bs = case pValue bs (skipWs bs 0) of
  PErr m -> Left m
  P v i  -> let j = skipWs bs i
            in if j >= B.length bs
                 then Right v
                 else Left ("trailing input after JSON value: "
                            ++ show (B.take 32 (B.drop j bs)))

-- | Where a parser got to, or why it stopped.
--
-- The cursor is an index into the line, and it travels /inside/ the result.
-- Saying the same thing as @Either String (a, B.ByteString)@ costs four heap
-- objects at every token -- the @Right@, the pair, and a fresh @ByteString@
-- slice with a fresh @ForeignPtr@ inside it -- and a 552 MB export has some
-- three hundred million tokens in it.  A strict constructor with an unpacked
-- @Int@ costs one, and the failure branch is not on any path a real file takes.
data P a = P !a {-# UNPACK #-} !Int | PErr String

isWs :: Char -> Bool
isWs c = c == ' ' || c == '\t' || c == '\r' || c == '\n'

-- | The first index at or after @i@ that is not whitespace.  An NDJSON line
-- written by an exporter has no whitespace in it at all, so this is almost
-- always @i@.
skipWs :: B.ByteString -> Int -> Int
skipWs bs = go
  where
    n = B.length bs
    go !i | i < n && isWs (B.index bs i) = go (i + 1)
          | otherwise                    = i

-- | The character at @i@, or @NUL@ past the end of the line.  Every caller is
-- asking whether it is some particular delimiter, and no delimiter is @NUL@, so
-- the end of input answers \"no\" without a 'Maybe' to allocate.
at :: B.ByteString -> Int -> Char
at bs i | i < B.length bs = B.index bs i
        | otherwise       = '\0'

-- | Does the line spell out this literal at @i@?
lit :: B.ByteString -> Int -> String -> Bool
lit bs = go
  where
    n = B.length bs
    go !i (c : cs) = i < n && B.index bs i == c && go (i + 1) cs
    go _  []       = True

-- | The substring between two indices, as bytes of its own.
--
-- Every caller is reading a string, and a string is the one thing here that
-- gets kept: it becomes a component of a 'Kernel.Name.Name' or the payload of a
-- literal, and those outlive the line by the whole run.  Taking a window
-- instead would keep the buffer under it too, and "Front.Mmap" explains why
-- that is the wrong thing to keep -- a single window pins the entire export,
-- and it is a mapping of the file rather than heap that ought to be free to go.
-- So the bytes are copied, which is a few hundred megabytes of short-lived
-- allocation across a large export and the difference between the file being
-- resident and the file being a file.
--
-- It is also, measured, the faster of the two, which was not the expectation.
-- Windows instead of copies made @init@ on one thread go 85.7s to 98.1s: a name
-- that is a window is read by touching the page of the mapping it came from,
-- and the pages a run's names live on are scattered across the whole export,
-- where copies are a few megabytes of heap next to each other.
slice :: B.ByteString -> Int -> Int -> B.ByteString
slice bs a b = B.copy (B.take (b - a) (B.drop a bs))

pValue :: B.ByteString -> Int -> P Json
pValue bs i
  | i >= B.length bs = PErr "unexpected end of input"
  | otherwise = case B.index bs i of
      '{' -> pObject bs (skipWs bs (i + 1))
      '[' -> pArray  bs (skipWs bs (i + 1))
      '"' -> case pString bs (i + 1) of
               P s j  -> P (JStr s) j
               PErr m -> PErr m
      't' | lit bs (i + 1) "rue"  -> P (JBool True)  (i + 4)
      'f' | lit bs (i + 1) "alse" -> P (JBool False) (i + 5)
      'n' | lit bs (i + 1) "ull"  -> P JNull         (i + 4)
      c | c == '-' || isDigit c   -> pNumber bs i
      c -> PErr ("unexpected character " ++ show c)

pObject :: B.ByteString -> Int -> P Json
pObject bs i
  | at bs i == '}' = P (JObj []) (i + 1)
  | otherwise      = go [] i
  where
    go acc s
      | s1 < 0    = PErr "expected '\"'"
      | otherwise = case pString bs s1 of
          PErr m -> PErr m
          P k s2
            | s3 < 0    -> PErr "expected ':'"
            | otherwise -> case pValue bs (skipWs bs s3) of
                PErr m -> PErr m
                P v s4 -> let acc' = (k, v) : acc
                              s5   = skipWs bs s4
                          in case at bs s5 of
                               ',' -> go acc' (skipWs bs (s5 + 1))
                               '}' -> P (JObj (reverse acc')) (s5 + 1)
                               _   -> PErr "expected ',' or '}' in object"
            where s3 = expect bs ':' (skipWs bs s2)
      where s1 = expect bs '"' (skipWs bs s)

pArray :: B.ByteString -> Int -> P Json
pArray bs i
  | at bs i == ']' = P (JArr []) (i + 1)
  | otherwise      = go [] i
  where
    go acc s = case pValue bs (skipWs bs s) of
      PErr m -> PErr m
      P v s1 -> let acc' = v : acc
                    s2   = skipWs bs s1
                in case at bs s2 of
                     ',' -> go acc' (skipWs bs (s2 + 1))
                     ']' -> P (JArr (reverse acc')) (s2 + 1)
                     _   -> PErr "expected ',' or ']' in array"

-- | The cursor just past the expected character, or @-1@ if it is not there.
-- A delimiter that is where it should be is the only case a real file has, and
-- reporting it as a number costs nothing to build and nothing to take apart.
expect :: B.ByteString -> Char -> Int -> Int
expect bs c i = if at bs i == c then i + 1 else -1

-- | Cursor is just past the opening quote.
pString :: B.ByteString -> Int -> P B.ByteString
pString bs i0 = scan i0
  where
    n = B.length bs
    -- Fast path: a string with no escapes in it is one slice of the line.
    scan !i
      | i >= n    = PErr "unterminated string"
      | c == '"'  = P (slice bs i0 i) (i + 1)
      | c == '\\' = slow [slice bs i0 i] i
      | otherwise = scan (i + 1)
      where c = B.index bs i
    -- Past the first backslash.  @acc@ is the pieces so far, reversed, and @i@
    -- points at a quote, a backslash, or the start of a plain run.
    slow acc !i
      | i >= n    = PErr "unterminated string"
      | c == '"'  = P (B.concat (reverse acc)) (i + 1)
      | c == '\\' = case pEscape bs (i + 1) of
          PErr m     -> PErr m
          P piece i' -> slow (piece : acc) i'
      | otherwise = run acc i (i + 1)
      where c = B.index bs i
    -- The plain run that started at @a@.
    run acc a !j
      | j >= n                = PErr "unterminated string"
      | c == '"' || c == '\\' = slow (slice bs a j : acc) j
      | otherwise             = run acc a (j + 1)
      where c = B.index bs j

pEscape :: B.ByteString -> Int -> P B.ByteString
pEscape bs i
  | i >= B.length bs = PErr "bad escape"
  | otherwise = case B.index bs i of
      '"'  -> P (B.singleton '"')  r
      '\\' -> P (B.singleton '\\') r
      '/'  -> P (B.singleton '/')  r
      'b'  -> P (B.singleton '\b') r
      'f'  -> P (B.singleton '\f') r
      'n'  -> P (B.singleton '\n') r
      'r'  -> P (B.singleton '\r') r
      't'  -> P (B.singleton '\t') r
      'u'  -> case hex4 bs r of
        PErr m  -> PErr m
        P h1 r1
          | h1 >= 0xD800 && h1 <= 0xDBFF
          , at bs r1 == '\\', at bs (r1 + 1) == 'u'
          -> case hex4 bs (r1 + 2) of
               PErr m -> PErr m
               P h2 r4
                 | h2 >= 0xDC00 && h2 <= 0xDFFF
                 -> let cp = 0x10000 + ((h1 - 0xD800) `shiftL` 10) .|. (h2 - 0xDC00)
                    in P (utf8 (fromIntegral cp)) r4
                 | otherwise -> P (utf8 (fromIntegral h1)) r1
          | otherwise -> P (utf8 (fromIntegral h1)) r1
      c -> PErr ("bad escape character " ++ show c)
  where
    r = i + 1

hex4 :: B.ByteString -> Int -> P Word32
hex4 bs i
  | i + 4 <= B.length bs, all (isHexDigit . B.index bs) [i .. i + 3] =
      P (foldl (\a j -> a * 16 + fromIntegral (digitToInt (B.index bs j))) 0
               [i .. i + 3])
        (i + 4)
  | otherwise = PErr "bad \\u escape"

-- | Encode a code point as UTF-8. Lean strings are UTF-8 and we keep them that way.
utf8 :: Int -> B.ByteString
utf8 cp
  | cp < 0x80    = B.pack [chr cp]
  | cp < 0x800   = B.pack [ chr (0xC0 .|. (cp `div` 64))
                          , cont cp ]
  | cp < 0x10000 = B.pack [ chr (0xE0 .|. (cp `div` 4096))
                          , cont (cp `div` 64), cont cp ]
  | otherwise    = B.pack [ chr (0xF0 .|. (cp `div` 262144))
                          , cont (cp `div` 4096), cont (cp `div` 64), cont cp ]
  where cont x = chr (0x80 .|. (x .&. 0x3F))

pNumber :: B.ByteString -> Int -> P Json
pNumber bs i
  | e == d    = PErr "expected digits"
  -- The export format only ever uses integers; reject anything fractional
  -- rather than silently truncating it.
  | c == '.' || c == 'e' || c == 'E' = PErr "non-integer number"
  | otherwise = P (JInt (if neg then negate (digits d e) else digits d e)) e
  where
    n   = B.length bs
    neg = at bs i == '-'
    d   = if neg then i + 1 else i
    e   = end d
    c   = at bs e
    end !j | j < n && isDigit (B.index bs j) = end (j + 1)
           | otherwise                       = j
    -- Almost every number in an export is a pool index of a few digits.
    -- Accumulating those in an 'Integer' allocates a bignum per digit; an 'Int'
    -- holds eighteen of them and costs one at the end.  Longer runs of digits
    -- are not a shape the format has, but they are a shape a file can have, so
    -- they get the exact arithmetic rather than a wrapped answer.
    digits a b
      | b - a <= 18 = toInteger (small a (0 :: Int))
      | otherwise   = big a 0
      where
        small !j !acc | j >= b    = acc
                      | otherwise = small (j + 1) (acc * 10 + val j)
        big   !j !acc | j >= b    = acc
                      | otherwise = big (j + 1) (acc * 10 + toInteger (val j))
    val j = fromEnum (B.index bs j) - 48

-- Accessors ------------------------------------------------------------------

asObject :: Json -> Either String [(B.ByteString, Json)]
asObject (JObj o) = Right o
asObject v        = Left ("expected object, got " ++ kindOf v)

-- | An object whose key set is exactly @ks@: every one of them present, none of
-- them twice, and nothing else.
--
-- Strictness here is not pedantry. The export format is the serialisation of a
-- fixed set of records, so a line carrying a field the format does not define
-- was not written by an exporter, and a reader that ignores the field is
-- deciding on its own what the line meant. A *missing* field is worse, because
-- then every reader downstream is free to invent a default for it — and the
-- fields most likely to go missing (@isUnsafe@, @binderInfo@, @safety@) are
-- exactly the ones whose default a forger would like to choose.
-- A record has a handful of fields, so the rule states itself as a quadratic
-- walk over two short lists that allocates nothing at all.  'audit' says the
-- same thing again, slowly and with a list of what went wrong, and only ever
-- runs to write the error message.
--
-- Doing it the other way round -- 'audit' first, and a fast path for the
-- expected field order -- looks cheaper and is not: the exporter writes a
-- record's fields in alphabetical order, this module lists them in the order
-- the format defines them, and for @app@, @lam@ and @forallE@ those two orders
-- differ.  So the fast path missed on most lines of a real export, and the
-- packing and 'nub'bing behind it cost about six per cent of a run.
record :: [String] -> Json -> Either String [(B.ByteString, Json)]
record ks v = do
  o <- asObject v
  if sameLength ks o && every o then Right o else audit o
  where
    sameLength (_ : ks') (_ : o') = sameLength ks' o'
    sameLength []        []       = True
    sameLength _         _        = False

    -- Every key of the object is one of @ks@ and does not occur again in it.
    -- With the lengths equal that is the whole rule: @ks@ has as many entries as
    -- the object has distinct keys, all of them drawn from @ks@, so none of
    -- @ks@ is missing.
    every ((kb, _) : rest) = any (sameKey kb) ks
                          && all ((/= kb) . fst) rest
                          && every rest
    every []               = True

    audit o =
      let got   = map fst o
          want  = map B.pack ks
          dups  = [k | k <- nub got, length (filter (== k) got) > 1]
          miss  = [k | k <- want, k `notElem` got]
          extra = [k | k <- nub got, k `notElem` want]
      in if null dups && null miss && null extra
           then Right o
           else Left (intercalate "; " (concat
                  [ report "repeated"   dups
                  , report "missing"    miss
                  , report "unexpected" extra ]))

    report _ []  = []
    report w [k] = [w ++ " field " ++ show (B.unpack k)]
    report w kss = [w ++ " fields " ++ intercalate ", " (map (show . B.unpack) kss)]

-- | Does an object key spell out this literal?
--
-- 'record' and 'field' run once per field of every line, which on a large
-- export is tens of millions of times, and the literals they are given are
-- 'String's.  Packing each one into a 'B.ByteString' just to compare it cost
-- about six per cent of a run over @init@; comparing in place costs no
-- allocation at all.
sameKey :: B.ByteString -> String -> Bool
sameKey b = go 0
  where
    n = B.length b
    go !i (c : cs) = i < n && B.index b i == c && go (i + 1) cs
    go !i []       = i == n

-- | The keys of an object that are not in @ignoring@. Used to find the one tag
-- that says what a line is, with the pool-index keys set aside.
--
-- Only the survivors are unpacked, which on a real export means one key per
-- line instead of all of them: a 'String' is two heap words per character, and
-- @ignoring@ is exactly the keys that were going to be thrown away.
tagsOf :: [String] -> [(B.ByteString, Json)] -> [String]
tagsOf ignoring o = [B.unpack kb | (kb, _) <- o, not (any (sameKey kb) ignoring)]

field :: [(B.ByteString, Json)] -> String -> Either String Json
field o k = go o
  where
    go ((kb, v) : rest) | sameKey kb k = Right v
                        | otherwise    = go rest
    go []                              = Left ("missing field " ++ show k)

optField :: [(B.ByteString, Json)] -> String -> Maybe Json
optField o k = go o
  where
    go ((kb, v) : rest) | sameKey kb k = Just v
                        | otherwise    = go rest
    go []                              = Nothing

asInt :: Json -> Either String Integer
asInt (JInt n) = Right n
asInt v        = Left ("expected integer, got " ++ kindOf v)

-- | Every number the export format contains is a natural: an index into a pool,
-- a de Bruijn index, a constructor position, a count of something. There is no
-- field anywhere in the format for which a negative value has a reading, so one
-- is a malformed file rather than an unusual one — and a negative that reached
-- a de Bruijn index or a field count would be read as an enormous positive by
-- something downstream.
asNat :: Json -> Either String Integer
asNat (JInt n)
  | n >= 0    = Right n
  | otherwise = Left ("expected a natural number, got " ++ show n)
asNat v       = Left ("expected a natural number, got " ++ kindOf v)

asString :: Json -> Either String B.ByteString
asString (JStr s) = Right s
asString v        = Left ("expected string, got " ++ kindOf v)

asBool :: Json -> Either String Bool
asBool (JBool b) = Right b
asBool v         = Left ("expected boolean, got " ++ kindOf v)

asArray :: Json -> Either String [Json]
asArray (JArr a) = Right a
asArray v        = Left ("expected array, got " ++ kindOf v)

kindOf :: Json -> String
kindOf JNull     = "null"
kindOf (JBool _) = "boolean"
kindOf (JInt _)  = "integer"
kindOf (JStr _)  = "string"
kindOf (JArr _)  = "array"
kindOf (JObj _)  = "object"
