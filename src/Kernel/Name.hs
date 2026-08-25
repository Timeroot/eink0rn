{-# LANGUAGE PatternSynonyms #-}
-- | Hierarchical names.
--
-- Names carry no logical content: the kernel treats them as opaque identifiers
-- for environment lookup.  They are structured only because the export format
-- is, and because a handful of built-in constants (@Nat@, @String@, ...) are
-- recognised by name when literals are expanded.
--
-- Each node caches a hash of the name below it.  Nothing depends on the hash
-- being any particular number: it exists so that the environment lookup on the
-- reduction hot path compares two @Int@s instead of walking two lists of
-- 'B.ByteString's.  As with 'Kernel.Expr.Expr', the cache is maintained by
-- pattern synonyms and the real constructors stay private.
module Kernel.Name
  ( Name
  , pattern Anon, pattern Str, pattern Num
  , nameHash
  , hashMix
  , anon
  , mkStr
  , mkNum
  , str
  , showName
  , nameNat, nameNatZero, nameNatSucc
  , nameString, nameStringOfByteArray
  , nameByteArray, nameValidUtf8, nameValidUtf8Intro, nameUtf8Encode
  , nameList, nameListNil, nameListCons
  , nameChar, nameCharOfNat
  , nameEq, nameEqRefl
  , nameBool, nameBoolTrue, nameBoolFalse
  , nameNatAdd, nameNatSub, nameNatMul, nameNatPow, nameNatPred
  , nameNatBEq, nameNatBLe, nameNatBLt, nameNatDiv, nameNatMod
  ) where

import           Data.Bits             (xor)
import qualified Data.ByteString.Char8 as B
import           Data.List             (intercalate)

-- | The @Int@ each compound constructor carries is the cached hash.
--
-- Deriving 'Eq' is still structural equality, since equal names hash equally;
-- the hash just decides most comparisons on its own.  Deriving 'Ord' orders by
-- hash first, which is not alphabetical but is a perfectly good total order --
-- names are only ever compared to key a map.
data Name
  = XAnon
  | XStr !Int !Name !B.ByteString
  | XNum !Int !Name !Integer
  deriving (Eq, Ord)

nameHash :: Name -> Int
nameHash XAnon        = 0
nameHash (XStr h _ _) = h
nameHash (XNum h _ _) = h

-- | The mixing step the caches are built from.  Exported because
-- 'Kernel.Expr.Expr' caches a hash the same way and there is no reason for two
-- of these.
hashMix :: Int -> Int -> Int
hashMix h x = (h * 33 `xor` x) * 0x9E3779B1

mix :: Int -> Int -> Int
mix = hashMix

hashBS :: B.ByteString -> Int
hashBS = B.foldl' (\h c -> h * 33 + fromEnum c) 5381

pattern Anon :: Name
pattern Anon = XAnon

pattern Str :: Name -> B.ByteString -> Name
pattern Str p s <- XStr _ p s
  where Str p s = XStr (mix (nameHash p) (hashBS s)) p s

pattern Num :: Name -> Integer -> Name
pattern Num p i <- XNum _ p i
  where Num p i = XNum (mix (nameHash p) (fromInteger i)) p i

{-# COMPLETE Anon, Str, Num #-}

instance Show Name where show = showName

anon :: Name
anon = Anon

mkStr :: Name -> B.ByteString -> Name
mkStr = Str

mkNum :: Name -> Integer -> Name
mkNum = Num

-- | Build a name from dot-separated ASCII components, e.g. @str "Nat.succ"@.
str :: String -> Name
str = foldl (\p c -> Str p (B.pack c)) Anon . splitDots
  where
    splitDots s = case break (== '.') s of
      (a, [])      -> [a]
      (a, _ : b)   -> a : splitDots b

showName :: Name -> String
showName n = case parts n [] of
  [] -> "[anonymous]"
  ps -> intercalate "." ps
  where
    parts Anon      acc = acc
    parts (Str p s) acc = parts p (B.unpack s : acc)
    parts (Num p i) acc = parts p (show i : acc)

-- Built-ins referenced by the literal expansion rules (see SPEC.md §Literals).

nameNat, nameNatZero, nameNatSucc :: Name
nameNat     = str "Nat"
nameNatZero = str "Nat.zero"
nameNatSucc = str "Nat.succ"

-- A string is a byte array that some list of characters encodes; these are the
-- pieces the encoding is spelt with.
nameString, nameStringOfByteArray, nameByteArray, nameValidUtf8,
  nameValidUtf8Intro, nameUtf8Encode :: Name
nameString            = str "String"
nameStringOfByteArray = str "String.ofByteArray"
nameByteArray         = str "ByteArray"
nameValidUtf8         = str "ByteArray.IsValidUTF8"
nameValidUtf8Intro    = str "ByteArray.IsValidUTF8.intro"
nameUtf8Encode        = str "List.utf8Encode"

nameList, nameListNil, nameListCons :: Name
nameList     = str "List"
nameListNil  = str "List.nil"
nameListCons = str "List.cons"

nameChar, nameCharOfNat :: Name
nameChar      = str "Char"
nameCharOfNat = str "Char.ofNat"

-- @Eq@ is here rather than with the audited constants in "Kernel.Canon" because
-- the expansion of a string literal is a term that mentions @Eq.refl@.
nameEq, nameEqRefl :: Name
nameEq     = str "Eq"
nameEqRefl = str "Eq.refl"

-- Arithmetic on numerals (see SPEC.md §6.5).  These are /candidates/: naming an
-- operation here only makes the kernel offer to compute it on bignums, and the
-- offer is taken up only for a definition whose own equations say it should be.

nameBool, nameBoolTrue, nameBoolFalse :: Name
nameBool      = str "Bool"
nameBoolTrue  = str "Bool.true"
nameBoolFalse = str "Bool.false"

nameNatAdd, nameNatSub, nameNatMul, nameNatPow, nameNatPred,
  nameNatBEq, nameNatBLe, nameNatBLt, nameNatDiv, nameNatMod :: Name
nameNatAdd  = str "Nat.add"
nameNatSub  = str "Nat.sub"
nameNatMul  = str "Nat.mul"
nameNatPow  = str "Nat.pow"
nameNatPred = str "Nat.pred"
nameNatBEq  = str "Nat.beq"
nameNatBLe  = str "Nat.ble"
nameNatBLt  = str "Nat.blt"
nameNatDiv  = str "Nat.div"
nameNatMod  = str "Nat.mod"
