{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE LambdaCase   #-}
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

import qualified Data.ByteString.Char8 as B
import           Data.Char             (isDigit)
import           Data.IntMap.Strict    (IntMap)
import qualified Data.IntMap.Strict    as IM
import           Front.Json
import           Kernel.Env            (Hint (..), QuotKind (..))
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
  { pNames  :: !(IntMap Name)
  , pLevels :: !(IntMap Level)
  , pExprs  :: !(IntMap Expr)
  }

emptyPools :: Pools
emptyPools = Pools (IM.singleton 0 Anon) (IM.singleton 0 LZero) IM.empty

-- | Parse a whole export.  Declarations come back in stream order.
parseExport :: B.ByteString -> Either String [ExDecl]
parseExport input = go (1 :: Int) emptyPools [] (B.lines input)
  where
    go _ _ acc [] = Right (reverse acc)
    go ln ps acc (l : ls) = case fastLine ps l of
      Just (Left err)  -> Left ("line " ++ show ln ++ ": " ++ err)
      Just (Right ps') -> go (ln + 1) ps' acc ls
      Nothing
        | B.null (B.dropWhile (`elem` " \t\r") l) -> go (ln + 1) ps acc ls
        | otherwise -> case step ps l of
            Left err          -> Left ("line " ++ show ln ++ ": " ++ err)
            Right (ps', mdec) -> go (ln + 1) ps' (maybe acc (: acc) mdec) ls

-- The three shapes that are most of a file ---------------------------------------
--
-- An export is overwhelmingly applications and binders, and each of the three is
-- written in exactly one shape, character for character:
--
-- > {"app":{"arg":N,"fn":M},"ie":K}
-- > {"ie":K,"lam":{"binderInfo":"B","body":N,"name":M,"type":T}}
-- > {"forallE":{"binderInfo":"B","body":N,"name":M,"type":T},"ie":K}
--
-- In @std@ those account for 9,272,681 of 10,023,185 lines, and across all four
-- corpora there is not one line of any of the three kinds that differs from its
-- shape by a byte.  Building a 'Json' value for each of them -- a list of pairs,
-- a boxed 'Integer' per index, a 'String' per key, all of it dead the moment the
-- pool lookups are done -- is most of what reading an export costs.
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
-- 'Nothing' is "not one of these shapes"; @Just (Left _)@ is "one of them, and
-- an index in it names a pool entry that does not exist".

fastLine :: Pools -> B.ByteString -> Maybe (Either String Pools)
fastLine ps l = case appLine ps l of
  Just r  -> Just r
  Nothing -> case lamLine ps l of
    Just r  -> Just r
    Nothing -> allLine ps l

-- | @{"app":{"arg":N,"fn":M},"ie":K}@.
appLine :: Pools -> B.ByteString -> Maybe (Either String Pools)
appLine ps l0 = do
  l1       <- lit appOpen l0
  (a,  l2) <- nat l1
  l3       <- lit appFn l2
  (f,  l4) <- nat l3
  l5       <- lit appIe l4
  (k,  l6) <- nat l5
  end =<< lit close l6
  pure $ do
    fn  <- exprIx ps f
    arg <- exprIx ps a
    Right (fileExpr k (App fn arg) ps)

-- | @{"ie":K,"lam":{"binderInfo":"B","body":N,"name":M,"type":T}}@.
lamLine :: Pools -> B.ByteString -> Maybe (Either String Pools)
lamLine ps l0 = do
  l1       <- lit lamOpen l0
  (k,  l2) <- nat l1
  l3       <- lit lamMid l2
  l4       <- binderInfoLit l3
  (b,  l5) <- nat l4
  l6       <- lit nameKey l5
  (nm, l7) <- nat l6
  l8       <- lit typeKey l7
  (t,  l9) <- nat l8
  la       <- lit lamEnd l9
  end la
  pure (binderAt ps Lam k nm t b)

-- | @{"forallE":{"binderInfo":"B","body":N,"name":M,"type":T},"ie":K}@.
allLine :: Pools -> B.ByteString -> Maybe (Either String Pools)
allLine ps l0 = do
  l1       <- lit allOpen l0
  l2       <- binderInfoLit l1
  (b,  l3) <- nat l2
  l4       <- lit nameKey l3
  (nm, l5) <- nat l4
  l6       <- lit typeKey l5
  (t,  l7) <- nat l6
  l8       <- lit allMid l7
  (k,  l9) <- nat l8
  end =<< lit close l9
  pure (binderAt ps Pi k nm t b)

-- | File a binder, resolving its three indices in the order 'readExpr' does.
binderAt :: Pools -> (Binder -> Expr -> Expr -> Expr)
         -> Int -> Int -> Int -> Int -> Either String Pools
binderAt ps con k nm t b = do
  n'   <- maybe (Left ("undefined name index " ++ show nm)) Right
                (IM.lookup nm (pNames ps))
  ty   <- exprIx ps t
  body <- exprIx ps b
  Right (fileExpr k (con (Binder n') ty body) ps)

exprIx :: Pools -> Int -> Either String Expr
exprIx ps i = maybe (Left ("undefined expression index " ++ show i)) Right
                    (IM.lookup i (pExprs ps))

fileExpr :: Int -> Expr -> Pools -> Pools
fileExpr k e ps = ps { pExprs = IM.insert k e (pExprs ps) }

lit :: B.ByteString -> B.ByteString -> Maybe B.ByteString
lit p s | p `B.isPrefixOf` s = Just (B.drop (B.length p) s)
        | otherwise          = Nothing

-- | Nothing left of the line.
end :: B.ByteString -> Maybe ()
end s = if B.null s then Just () else Nothing

-- | A run of digits, as a number.
--
-- 'B.readInt' would also take a sign, and -- despite what its name suggests
-- about the range it reads -- wraps silently on a number too large for an 'Int'
-- rather than declining to read it.  A wrapped index that landed on a pool entry
-- that happens to exist would be read as naming it.  So the run is measured
-- first, and anything but one to eighteen digits -- eighteen being as many as
-- cannot overflow -- is left to 'step', which checks the range properly and says
-- so.
nat :: B.ByteString -> Maybe (Int, B.ByteString)
nat s | d < 1 || d > 18 = Nothing
      | otherwise       = B.readInt s
  where d = digits 0
        digits !j | j < B.length s && isDigit (B.index s j) = digits (j + 1)
                  | otherwise                              = j

-- | One of the four binder annotations, followed by the key that comes after it.
--
-- The annotation itself is discarded, exactly as 'binderInfoOf' discards it; it
-- is matched only because a line carrying one this reader does not know is a
-- line written against a format it does not know.
binderInfoLit :: B.ByteString -> Maybe B.ByteString
binderInfoLit s = go binderInfoLits
  where
    go []       = Nothing
    go (p : pr) = case lit p s of
      Just t  -> Just t
      Nothing -> go pr

-- | The literal stretches, packed once at the top level rather than at each of
-- ten million comparisons.
appOpen, appFn, appIe, lamOpen, lamMid, lamEnd, allOpen, allMid,
  nameKey, typeKey, close :: B.ByteString
appOpen = B.pack "{\"app\":{\"arg\":"
appFn   = B.pack ",\"fn\":"
appIe   = B.pack "},\"ie\":"
lamOpen = B.pack "{\"ie\":"
lamMid  = B.pack ",\"lam\":{\"binderInfo\":\""
lamEnd  = B.pack "}}"
allOpen = B.pack "{\"forallE\":{\"binderInfo\":\""
allMid  = B.pack "},\"ie\":"
nameKey = B.pack ",\"name\":"
typeKey = B.pack ",\"type\":"
close   = B.pack "}"

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
      pure (put (IM.insert k x (get ps)), Nothing)

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
  maybe (Left ("undefined name index " ++ show i)) Right (IM.lookup i (pNames ps))

levelAt :: Pools -> Json -> Either String Level
levelAt ps j = do
  i <- natOf j
  maybe (Left ("undefined level index " ++ show i)) Right (IM.lookup i (pLevels ps))

exprAt :: Pools -> Json -> Either String Expr
exprAt ps j = do
  i <- natOf j
  maybe (Left ("undefined expression index " ++ show i)) Right (IM.lookup i (pExprs ps))

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
