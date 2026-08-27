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
parseJsonLine bs = do
  (v, rest) <- pValue (skipWs bs)
  let rest' = skipWs rest
  if B.null rest'
    then Right v
    else Left ("trailing input after JSON value: " ++ show (B.take 32 rest'))

isWs :: Char -> Bool
isWs c = c == ' ' || c == '\t' || c == '\r' || c == '\n'

-- | An NDJSON line written by an exporter has no whitespace in it at all, and
-- 'B.dropWhile' allocates a fresh slice even when it drops nothing.  So look
-- before dropping: the answer is almost always the argument.
skipWs :: B.ByteString -> B.ByteString
skipWs bs
  | B.null bs || not (isWs (B.head bs)) = bs
  | otherwise                           = B.dropWhile isWs bs

pValue :: B.ByteString -> Either String (Json, B.ByteString)
pValue bs
  | B.null bs = Left "unexpected end of input"
  | otherwise = case B.head bs of
      '{' -> pObject (skipWs r)
      '[' -> pArray (skipWs r)
      '"' -> do (s, r') <- pString r; pure (JStr s, r')
      't' | Just r' <- B.stripPrefix (B.pack "rue") r  -> Right (JBool True, r')
      'f' | Just r' <- B.stripPrefix (B.pack "alse") r -> Right (JBool False, r')
      'n' | Just r' <- B.stripPrefix (B.pack "ull") r  -> Right (JNull, r')
      c | c == '-' || isDigit c -> pNumber bs
      c -> Left ("unexpected character " ++ show c)
  where r = B.tail bs

-- | The character the input is looking at, or @NUL@ at the end of it.  Every
-- caller is asking whether it is some particular delimiter, and no delimiter is
-- @NUL@, so the end of input answers \"no\" without a 'Maybe' to allocate.
nextChar :: B.ByteString -> Char
nextChar s = if B.null s then '\0' else B.head s

pObject :: B.ByteString -> Either String (Json, B.ByteString)
pObject bs
  | nextChar bs == '}' = Right (JObj [], B.tail bs)
  | otherwise          = go [] bs
  where
    go acc s = do
      s1 <- expect '"' (skipWs s)
      (k, s2) <- pString s1
      s3 <- expect ':' (skipWs s2)
      (v, s4) <- pValue (skipWs s3)
      let acc' = (k, v) : acc
          s5   = skipWs s4
      case nextChar s5 of
        ',' -> go acc' (skipWs (B.tail s5))
        '}' -> Right (JObj (reverse acc'), B.tail s5)
        _   -> Left "expected ',' or '}' in object"

pArray :: B.ByteString -> Either String (Json, B.ByteString)
pArray bs
  | nextChar bs == ']' = Right (JArr [], B.tail bs)
  | otherwise          = go [] bs
  where
    go acc s = do
      (v, s1) <- pValue (skipWs s)
      let acc' = v : acc
          s2   = skipWs s1
      case nextChar s2 of
        ',' -> go acc' (skipWs (B.tail s2))
        ']' -> Right (JArr (reverse acc'), B.tail s2)
        _   -> Left "expected ',' or ']' in array"

expect :: Char -> B.ByteString -> Either String B.ByteString
expect c s
  | nextChar s == c = Right (B.tail s)
  | otherwise       = Left ("expected " ++ show c)

-- | Cursor is just past the opening quote.
pString :: B.ByteString -> Either String (B.ByteString, B.ByteString)
pString s0 =
  let (chunk, rest) = B.break (\c -> c == '"' || c == '\\') s0
  in case nextChar rest of
       '"'  -> Right (chunk, B.tail rest)          -- fast path: no escapes
       '\\' -> do (parts, r) <- slow [chunk] rest
                  pure (B.concat parts, r)
       _    -> Left "unterminated string"
  where
    slow acc s = case nextChar s of
      '"'  -> Right (reverse acc, B.tail s)
      '\\' -> do
        (piece, r') <- pEscape (B.tail s)
        let (chunk, rest) = B.break (\c -> c == '"' || c == '\\') r'
        slow (chunk : piece : acc) rest
      _ -> Left "unterminated string"

pEscape :: B.ByteString -> Either String (B.ByteString, B.ByteString)
pEscape s = case B.uncons s of
  Nothing -> Left "bad escape"
  Just (c, r) -> case c of
    '"'  -> Right (B.singleton '"',  r)
    '\\' -> Right (B.singleton '\\', r)
    '/'  -> Right (B.singleton '/',  r)
    'b'  -> Right (B.singleton '\b', r)
    'f'  -> Right (B.singleton '\f', r)
    'n'  -> Right (B.singleton '\n', r)
    'r'  -> Right (B.singleton '\r', r)
    't'  -> Right (B.singleton '\t', r)
    'u'  -> do
      (h1, r1) <- hex4 r
      if h1 >= 0xD800 && h1 <= 0xDBFF
        then case B.uncons r1 of
               Just ('\\', r2) | Just ('u', r3) <- B.uncons r2 -> do
                 (h2, r4) <- hex4 r3
                 if h2 >= 0xDC00 && h2 <= 0xDFFF
                   then let cp = 0x10000 + ((h1 - 0xD800) `shiftL` 10) .|. (h2 - 0xDC00)
                        in Right (utf8 (fromIntegral cp), r4)
                   else Right (utf8 (fromIntegral h1), r1)
               _ -> Right (utf8 (fromIntegral h1), r1)
        else Right (utf8 (fromIntegral h1), r1)
    _ -> Left ("bad escape character " ++ show c)
  where
    hex4 t
      | B.length t >= 4, B.all isHexDigit (B.take 4 t) =
          Right (B.foldl' (\a d -> a * 16 + fromIntegral (digitToInt d)) (0 :: Word32) (B.take 4 t), B.drop 4 t)
      | otherwise = Left "bad \\u escape"

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

pNumber :: B.ByteString -> Either String (Json, B.ByteString)
pNumber bs =
  let neg      = nextChar bs == '-'
      r0       = if neg then B.tail bs else bs
      (ds, r1) = B.span isDigit r0
  in if B.null ds
       then Left "expected digits"
       else
         -- The export format only ever uses integers; reject anything fractional
         -- rather than silently truncating it.
         case nextChar r1 of
           c | c == '.' || c == 'e' || c == 'E' -> Left "non-integer number"
           _ -> let n = digits ds
                in Right (JInt (if neg then negate n else n), r1)
  where
    -- Almost every number in an export is a pool index of a few digits.
    -- Accumulating those in an 'Integer' allocates a bignum per digit; an 'Int'
    -- holds eighteen of them and costs one at the end.  Longer runs of digits
    -- are not a shape the format has, but they are a shape a file can have, so
    -- they get the exact arithmetic rather than a wrapped answer.
    digits ds
      | B.length ds <= 18 = toInteger (B.foldl' (\a d -> a * 10 + val d) (0 :: Int) ds)
      | otherwise         = B.foldl' (\a d -> a * 10 + toInteger (val d)) 0 ds
    val d = fromEnum d - 48

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
tagsOf :: [String] -> [(B.ByteString, Json)] -> [String]
tagsOf ignoring o = [k | (kb, _) <- o, let k = B.unpack kb, k `notElem` ignoring]

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
