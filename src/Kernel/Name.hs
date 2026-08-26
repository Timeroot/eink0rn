{-# LANGUAGE MagicHash       #-}
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
  , pattern Anon, pattern Str, pattern Num, pattern Priv
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
import           GHC.Exts              (isTrue#, reallyUnsafePtrEquality#)

-- | The @Int@ each compound constructor carries is the cached hash.
--
-- 'Ord' is derived, which orders by constructor and then by hash: not
-- alphabetical, but a perfectly good total order, and names are only ever
-- compared to key a map.
--
-- @XPriv@ is a second root, alongside the anonymous one, that the export
-- reader cannot reach: "Front.Export" builds every name it reads by 'mkStr'
-- and 'mkNum' from 'anon', so no name coming out of a file is ever rooted
-- there.  It is what "Front.Lower" hangs the constants it invents from -- see
-- 'Priv'.
data Name
  = XAnon
  | XStr !Int !Name !B.ByteString
  | XNum !Int !Name !Integer
  | XPriv !Int !Int
  deriving (Ord)

-- | Structural equality, which is what the derived instance would be, with a
-- pointer test in front of each case.
--
-- Unequal names are settled by the cached hash, which is what it is for.  Equal
-- names are the expensive case, and they are also the case that is usually the
-- same object: the export format interns names in a pool, so every reference to
-- @Nat.succ@ in a file is the very same 'Name', and the constant the reduction
-- hot path looks up is pointer-equal to the key stored in the environment.  A
-- pointer test settles that in one instruction instead of walking the chain and
-- comparing a 'B.ByteString' at every link.  It is only ever a fast path: a
-- @False@ from it means nothing, and the walk still runs.  Recursing through
-- @(==)@ retries the test at every link, so a fresh @Foo.rec@ built by the
-- kernel still stops at its pooled @Foo@.
--
-- The test comes *after* the match, not before it.  Writing it in front of the
-- whole instance -- @ptrEq a b || slow a b@ -- costs half a per cent of the
-- allocation of a run over @init@, because the arguments then have to be boxed
-- for a function that does not scrutinise them.
--
-- 'Kernel.Expr.Expr' does the same thing with the same two tests.  The pointer
-- primitive is spelled out again here rather than shared, because "Kernel.Expr"
-- imports this module for 'nameHash'.
instance Eq Name where
  XAnon == XAnon = True
  x@(XStr h1 p1 s1) == y@(XStr h2 p2 s2) =
    ptrEq x y || (h1 == h2 && s1 == s2 && p1 == p2)
  x@(XNum h1 p1 i1) == y@(XNum h2 p2 i2) =
    ptrEq x y || (h1 == h2 && i1 == i2 && p1 == p2)
  XPriv _ a == XPriv _ b = a == b
  _ == _ = False

ptrEq :: Name -> Name -> Bool
ptrEq a b = isTrue# (reallyUnsafePtrEquality# a b)
{-# INLINE ptrEq #-}

nameHash :: Name -> Int
nameHash XAnon         = 0
nameHash (XStr h _ _)  = h
nameHash (XNum h _ _)  = h
nameHash (XPriv h _)   = h

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

-- | @Priv k@ is the root of the @k@th private namespace.
--
-- The kernel's front end has to invent constants: the nesting compilation of
-- SPEC.md §9.1 needs a name for each specialised container, and the flattening
-- of §9.3 needs one for the tag type, the flat type and their recursors.  An
-- invented name must not be one the file also uses, or the file could say
-- something about a constant the kernel meant to keep to itself.
--
-- Rooting them here settles that by construction rather than by searching for
-- an unused suffix: 'Front.Export' reads names out of the file's name pool,
-- and every entry in that pool is 'anon', a 'Str' or a 'Num', so no name a
-- file can write is equal to one rooted at a 'Priv'.  Distinct @k@ give
-- disjoint namespaces, which is what lets one run invent names for many blocks
-- without them colliding with each other.
pattern Priv :: Int -> Name
pattern Priv k <- XPriv _ k
  where Priv k = XPriv (mix 0x1F0 k) k

{-# COMPLETE Anon, Str, Num, Priv #-}

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
    parts (Priv k)  acc = ("_private" ++ show k) : acc

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
