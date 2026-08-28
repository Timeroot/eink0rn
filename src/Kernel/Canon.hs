-- | Stored canonical forms: what the constants the kernel gives a meaning to
-- are /supposed/ to look like.
--
-- Nothing in this module is believed.  It is a table of expectations, and every
-- entry is compared against what the file actually declared before anything is
-- done with it.  Two clients:
--
-- * "Kernel.Check" consults 'natOpCanon' before computing an arithmetic
--   operation on bignums, so that the shortcut is licensed by the declaration
--   rather than by the name (SPEC.md §6.5);
--
-- * "Front.Lower" consults 'stdPins' when the operator asks for the standard
--   constants to be audited -- @False@, @Eq@, @Iff@, @Nonempty@, the three
--   axioms and the quotient package -- so that a file which redefines one of
--   them cannot pass itself off as ordinary mathematics (SPEC.md §12.5).
--
-- Everything here was read off a real export.  The forms are written in the
-- kernel's own term language rather than copied as syntax, which is what lets
-- them be compared up to definitional equality and up to the file's choice of
-- universe-parameter names.
--
-- What is deliberately /not/ stored is the body of any definition.  An exported
-- @Nat.add@ is a @Nat.brecOn@ over an auto-generated matcher, named with
-- hygienic identifiers that carry a hash of the module they were elaborated in;
-- pinning that would pin the compiler's mood on the day, not the arithmetic.
-- The stored specification of an operation is its /type/ together with its
-- /defining equations/, which is what an implementation has to satisfy however
-- it is written, and which -- unlike a body -- says what the operation
-- computes.  See the section header in "Kernel.Check" for why the equations are
-- enough.
--
-- Two operations, @div@ and @mod@, have no defining equations to state, and are
-- held against a battery of closed test cases instead.  That is a weaker kind of
-- licence and is marked as such: see 'nocProbes'.
module Kernel.Canon
  ( -- * Inductive types
    CanonInd (..)
  , CanonCtor (..)
  , Canonical
  , natCanon
  , boolCanon
    -- * The arithmetic surface
  , NatOpCanon (..)
  , natOpCanon
  , natOpNames
  , natProbeArgs
    -- * The standard constants
  , StdPin (..)
  , stdPins
  , quotModule
  ) where

import           Kernel.Env
import           Kernel.Expr
import           Kernel.Level
import           Kernel.Name

-- Notation ---------------------------------------------------------------------

pi_ :: String -> Expr -> Expr -> Expr
pi_ n = Pi (Binder (str n))

prop_ :: Expr
prop_ = Sort LZero

type0 :: Expr
type0 = Sort (LSucc LZero)

nat :: Expr
nat = Const nameNat []

bool :: Expr
bool = Const nameBool []

-- | A stored type, as a function of the universe-parameter names the /file/
-- chose.  A canonical form is written with 'lvlAt' rather than with names of
-- our own, so that comparing against a file which spells its parameter @u_1@
-- asks about the type and not about the spelling.
type Canonical = [Name] -> Expr

-- | The file's @i@th universe parameter.  Every caller checks the arity first,
-- so the fallback is unreachable; it is there so that this is a total function
-- and a miscount can only ever make a comparison fail.
lvlAt :: Int -> [Name] -> Level
lvlAt i us
  | i < length us = LParam (us !! i)
  | otherwise     = LZero

-- | An inductive type as it is expected to have been declared.
data CanonInd = CanonInd
  { ciName      :: Name
  , ciNumLevels :: Int
  , ciType      :: Canonical
  , ciNumParams :: Int
  , ciNumIdx    :: Int
  , ciCtors     :: [CanonCtor]   -- ^ in constructor-index order
  }

data CanonCtor = CanonCtor
  { ccName      :: Name
  , ccNumFields :: Int
  , ccType      :: Canonical
  }

-- Inductive types the kernel reads meaning into --------------------------------

-- | @Nat@, the type a numeral literal abbreviates and the one the arithmetic
-- shortcuts compute in.
natCanon :: CanonInd
natCanon = CanonInd
  { ciName      = nameNat
  , ciNumLevels = 0
  , ciType      = const type0
  , ciNumParams = 0
  , ciNumIdx    = 0
  , ciCtors     =
      [ CanonCtor nameNatZero 0 (const nat)
      , CanonCtor nameNatSucc 1 (const (mkArrow nat nat))
      ]
  }

-- | @Bool@, which the comparison shortcuts produce.
boolCanon :: CanonInd
boolCanon = CanonInd
  { ciName      = nameBool
  , ciNumLevels = 0
  , ciType      = const type0
  , ciNumParams = 0
  , ciNumIdx    = 0
  , ciCtors     =
      [ CanonCtor nameBoolFalse 0 (const bool)
      , CanonCtor nameBoolTrue  0 (const bool)
      ]
  }

-- The arithmetic surface --------------------------------------------------------

-- | What an accelerated operation must be, for the shortcut to be taken.
data NatOpCanon = NatOpCanon
  { nocType :: Expr
    -- ^ the type it must be declared at, with no universe parameters
  , nocInds :: [CanonInd]
    -- ^ the inductive types that type and those equations are stated over
  , nocDeps :: [Name]
    -- ^ other accelerated operations the equations mention, which therefore
    -- have to be established first
  , nocLaws :: Expr -> Expr -> [(Expr, Expr)]
    -- ^ defining equations, given two fresh locals of type @Nat@.  Empty for an
    -- operation that has none to state: see 'natOpCanon'.
  , nocProbes :: [(Expr, Expr)]
    -- ^ closed conversions the operation must satisfy, for an operation whose
    -- equations cannot be stated.  Strictly weaker than 'nocLaws': an equation
    -- between open terms settles every numeral case at once, by induction,
    -- whereas a probe settles the one case it names.  Only @div@ and @mod@ have
    -- these, and only because nothing better exists for them.
  }

-- | The stored specification of each operation the kernel offers to compute.
--
-- @div@ and @mod@ are the two odd ones.  Neither has a defining equation the
-- kernel could check: an exported @Nat.div@ recurses on a fuel argument under a
-- guard @0 < y@, so @div x y@ with @x@ and @y@ open gets stuck on a comparison
-- it cannot decide, and no amount of rewriting the equation moves that.  What
-- such a definition /does/ do is compute: handed two numerals it reduces to a
-- numeral, by the file's own rules and with no help from the kernel.  So they
-- are held against 'natProbeArgs' -- a fixed list of numeral pairs on which the
-- file's own @div@ and @mod@ must reduce to the right answers.  Every probe that
-- passes is an equality the file's theory already had; what the kernel adds is
-- the extrapolation from the pairs tried to the rest, and that is the whole of
-- what this licence assumes.  See SPEC.md §6.5.
--
-- @Nat.le@ has no entry at all, for a plainer reason: it is an inductive family
-- in @Prop@, not a function, and has nothing to compute.  The decidable
-- comparisons that stand in for it -- @Nat.decLe@, @Nat.decLt@ -- reduce
-- through @ble@ and @blt@, which do.
natOpCanon :: Name -> Maybe NatOpCanon
natOpCanon n
  | n == nameNatPred = Just $ arith 1 $ \x _ ->
      [ (f [z],        z)
      , (f [s x],      x) ]
  | n == nameNatAdd  = Just $ arith 2 $ \x y ->
      [ (f [x, z],     x)
      , (f [x, s y],   s (f [x, y])) ]
  | n == nameNatSub  = Just $ needs [nameNatPred] $ arith 2 $ \x y ->
      [ (f [x, z],     x)
      , (f [x, s y],   p (f [x, y])) ]
  | n == nameNatMul  = Just $ needs [nameNatAdd] $ arith 2 $ \x y ->
      [ (f [x, z],     z)
      , (f [x, s y],   add [f [x, y], x]) ]
  | n == nameNatPow  = Just $ needs [nameNatMul] $ arith 2 $ \x y ->
      [ (f [x, z],     s z)
      , (f [x, s y],   mul [f [x, y], x]) ]
  | n == nameNatBEq  = Just $ cmp $ \x y ->
      [ (f [z, z],     true)
      , (f [s x, z],   false)
      , (f [z, s y],   false)
      , (f [s x, s y], f [x, y]) ]
  | n == nameNatBLe  = Just $ cmp $ \x y ->
      [ (f [z, z],     true)
      , (f [z, s y],   true)
      , (f [s x, z],   false)
      , (f [s x, s y], f [x, y]) ]
  -- @blt@ is settled by one equation rather than four: it says outright which
  -- comparison it is, and @ble@ has already been pinned to that comparison.
  | n == nameNatBLt  = Just $ needs [nameNatBLe] $ cmp $ \x y ->
      [ (f [x, y],     ble [s x, y]) ]
  | n == nameNatDiv  = Just $ probed (\a b -> if b == 0 then 0 else a `div` b)
                            $ arith 2 noLaws
  | n == nameNatMod  = Just $ probed (\a b -> if b == 0 then a else a `mod` b)
                            $ arith 2 noLaws
  | otherwise        = Nothing
  where
    arity k ty laws = NatOpCanon
      { nocType = iterate (mkArrow nat) ty !! k
      , nocInds = [natCanon], nocDeps = [], nocLaws = laws, nocProbes = [] }
    arith k    = arity k nat
    cmp   laws = (arity 2 bool laws) { nocInds = [natCanon, boolCanon] }
    needs ds c = c { nocDeps = ds }
    noLaws _ _ = []

    probed g c = c { nocProbes = [ (mkApps (Const n []) [NatLit a, NatLit b]
                                  , NatLit (g a b))
                                 | (a, b) <- natProbeArgs ] }

    f     = mkApps (Const n [])
    add   = mkApps (Const nameNatAdd [])
    mul   = mkApps (Const nameNatMul [])
    ble   = mkApps (Const nameNatBLe [])
    p e   = App (Const nameNatPred []) e
    s e   = App (Const nameNatSucc []) e
    z     = Const nameNatZero []
    true  = Const nameBoolTrue []
    false = Const nameBoolFalse []

-- | Every name 'natOpCanon' has an entry for.
--
-- The list exists so that the licences can be established all at once rather
-- than one at a time as reduction happens on them; see
-- 'Kernel.Check.warmLicences'.  Keep it in step with 'natOpCanon' -- a name
-- missing from here costs a licence, never a wrong one, since nothing consults
-- the list to decide anything.
natOpNames :: [Name]
natOpNames =
  [ nameNatPred, nameNatAdd, nameNatSub, nameNatMul, nameNatPow
  , nameNatBEq, nameNatBLe, nameNatBLt, nameNatDiv, nameNatMod ]

-- | The numeral pairs @div@ and @mod@ are tried on.
--
-- Two parts, and the shapes matter more than the numbers.  The square is
-- exhaustive, so every relation the two arguments can stand in appears in it:
-- zero divisor, zero dividend, @a \< b@, @a = b@, @a \> b@, and every remainder of
-- every divisor up to twelve.  The ladder then walks past the square, one pair at
-- a time and at no regular spacing, so that a @div@ agreeing with division only
-- where it was obviously going to be looked at would have to keep agreeing
-- somewhere less obvious.  Between them the ladder's pairs are a divisor of one, a
-- divisor larger than the dividend, two equal pairs, exact quotients, maximal
-- remainders, powers of two and their neighbours, and a large zero divisor.
--
-- The ceiling is low on purpose, and the ladder is short for the same reason.  A
-- file's own @div@ recurses on a fuel argument taken from the dividend, and each
-- step of that recursion subtracts -- so a probe costs about the square of the
-- dividend, and the ladder as written already costs several times the whole
-- square.  Probing at numerals the size of the ones this licence exists to make
-- cheap would cost exactly what the licence is meant to save.  So the battery is
-- finite and affordable, and 'nocProbes' says plainly what that buys.
natProbeArgs :: [(Integer, Integer)]
natProbeArgs =
  [ (a, b) | a <- [0 .. 12], b <- [0 .. 12] ]
  ++
  [ (13, 4), (17, 17), (19, 20), (23, 1), (32, 5), (33, 8), (40, 7), (47, 16)
  , (53, 53), (64, 3), (65, 64), (71, 9), (91, 13), (100, 10), (127, 0), (128, 7) ]

-- The standard constants ---------------------------------------------------------

-- | What a pinned constant must be.
data StdPin
  = PinInd CanonInd
  | PinAxiom Int Canonical   -- ^ number of universe parameters, and type
  | PinQuot QuotKind

-- | The names @--pin-std@ audits.
--
-- Chosen as the transitive support of Lean's three axioms.  @propext@,
-- @Quot.sound@ and @Classical.choice@ are the only things in an ordinary
-- development that are asserted rather than proved, so they are where a forged
-- environment would put its thumb; and each is stated in terms of constants the
-- file also owns -- @Eq@, @Iff@, @Nonempty@, @Quot@ -- which is where the thumb
-- would actually go, since restating an axiom is conspicuous and redefining
-- what it is stated over is not.  @False@ is in the list because it is the
-- target: a @False@ with a constructor makes every other check beside the
-- point.
stdPins :: [(Name, StdPin)]
stdPins =
  [ (nameFalse, PinInd CanonInd
      { ciName = nameFalse, ciNumLevels = 0, ciType = const prop_
      , ciNumParams = 0, ciNumIdx = 0, ciCtors = [] })

  -- Eq : ∀ (α : Sort u) (a b : α), Prop, with α and a parameters, b the index
  , (nameEq, PinInd CanonInd
      { ciName = nameEq, ciNumLevels = 1
      , ciType = \us -> pi_ "A" (Sort (lvlAt 0 us)) $
                        pi_ "a" (BVar 0) $
                        pi_ "b" (BVar 1) prop_
      , ciNumParams = 2, ciNumIdx = 1
      , ciCtors = [ CanonCtor nameEqRefl 0 $ \us ->
                      pi_ "A" (Sort (lvlAt 0 us)) $
                      pi_ "a" (BVar 0) $
                      mkApps (Const nameEq [lvlAt 0 us]) [BVar 1, BVar 0, BVar 0] ] })

  -- Iff : Prop → Prop → Prop
  , (nameIff, PinInd CanonInd
      { ciName = nameIff, ciNumLevels = 0
      , ciType = const (pi_ "a" prop_ (pi_ "b" prop_ prop_))
      , ciNumParams = 2, ciNumIdx = 0
      , ciCtors = [ CanonCtor nameIffIntro 2 $ const $
                      pi_ "a"   prop_ $
                      pi_ "b"   prop_ $
                      pi_ "mp"  (mkArrow (BVar 1) (BVar 0)) $
                      pi_ "mpr" (mkArrow (BVar 1) (BVar 2)) $
                      mkApps (Const nameIff []) [BVar 3, BVar 2] ] })

  -- Nonempty : Sort u → Prop
  , (nameNonempty, PinInd CanonInd
      { ciName = nameNonempty, ciNumLevels = 1
      , ciType = \us -> pi_ "A" (Sort (lvlAt 0 us)) prop_
      , ciNumParams = 1, ciNumIdx = 0
      , ciCtors = [ CanonCtor nameNonemptyIntro 1 $ \us ->
                      pi_ "A" (Sort (lvlAt 0 us)) $
                      mkArrow (BVar 0)
                              (App (Const nameNonempty [lvlAt 0 us]) (BVar 0)) ] })

  -- propext : ∀ (a b : Prop), Iff a b → Eq.{1} Prop a b
  , (namePropext, PinAxiom 0 $ const $
      pi_ "a" prop_ $
      pi_ "b" prop_ $
      mkArrow (mkApps (Const nameIff []) [BVar 1, BVar 0])
              (mkApps (Const nameEq [LSucc LZero]) [prop_, BVar 1, BVar 0]))

  -- Classical.choice : ∀ {α : Sort u}, Nonempty α → α
  , (nameChoice, PinAxiom 1 $ \us ->
      pi_ "A" (Sort (lvlAt 0 us)) $
      mkArrow (App (Const nameNonempty [lvlAt 0 us]) (BVar 0)) (BVar 0))

  -- Quot.sound : ∀ {α r} {a b : α}, r a b → Quot.mk r a = Quot.mk r b
  , (nameQuotSound, PinAxiom 1 $ \us ->
      pi_ "A" (Sort (lvlAt 0 us)) $
      pi_ "r" (pi_ "_" (BVar 0) (pi_ "_" (BVar 1) prop_)) $
      pi_ "a" (BVar 1) $
      pi_ "b" (BVar 2) $
      pi_ "h" (mkApps (BVar 2) [BVar 1, BVar 0]) $
      mkApps (Const nameEq [lvlAt 0 us])
             [ mkApps (Const nameQuot   [lvlAt 0 us]) [BVar 4, BVar 3]
             , mkApps (Const nameQuotMk [lvlAt 0 us]) [BVar 4, BVar 3, BVar 2]
             , mkApps (Const nameQuotMk [lvlAt 0 us]) [BVar 4, BVar 3, BVar 1] ])

  -- The four quotient primitives have their types pinned already, when they are
  -- admitted (SPEC.md §10); all that is left to audit is that each name really
  -- is the primitive it is named after, and not an ordinary definition.
  , (nameQuot,     PinQuot QType)
  , (nameQuotMk,   PinQuot QCtor)
  , (nameQuotLift, PinQuot QLift)
  , (nameQuotInd,  PinQuot QInd)
  ]

-- | The quotient primitives, which are audited as a unit: a file that has any
-- of these has to have all of them.
--
-- @Quot.sound@ is /not/ one of them.  It is exported as an ordinary axiom
-- rather than as a quotient primitive, and so appears only when something
-- reaches it; most exports that use quotients at all do not have it.  The four
-- below arrive together or not at all.
quotModule :: [Name]
quotModule = [nameQuot, nameQuotMk, nameQuotLift, nameQuotInd]

-- ('nameEq' and 'nameEqRefl' are in "Kernel.Name" with the other constants the
-- kernel builds terms out of: a string literal's expansion needs @Eq.refl@.)
nameFalse, nameIff, nameIffIntro, nameNonempty,
  nameNonemptyIntro, namePropext, nameChoice, nameQuot, nameQuotMk,
  nameQuotLift, nameQuotInd, nameQuotSound :: Name
nameFalse         = str "False"
nameIff           = str "Iff"
nameIffIntro      = str "Iff.intro"
nameNonempty      = str "Nonempty"
nameNonemptyIntro = str "Nonempty.intro"
namePropext       = str "propext"
nameChoice        = str "Classical.choice"
nameQuot          = str "Quot"
nameQuotMk        = str "Quot.mk"
nameQuotLift      = str "Quot.lift"
nameQuotInd       = str "Quot.ind"
nameQuotSound     = str "Quot.sound"
