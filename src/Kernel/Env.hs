-- | The environment: the set of accepted constants.
--
-- The core admits only five kinds of constant.  An inductive type here is
-- always /flat/: a block of one or more mutually recursive families, each a
-- plain telescope of parameters and indices.  Nesting -- a family occurring
-- under some other type constructor -- is not part of the core; "Front.Lower"
-- compiles it into an equivalent flat block before the kernel sees it.
module Kernel.Env
  ( ConstInfo (..)
  , DefInfo (..)
  , Hint (..)
  , IndInfo (..)
  , CtorInfo (..)
  , RecInfo (..)
  , RecRule (..)
  , QuotKind (..)
  , AccelMode (..)
  , Licences (..)
  , noLicences
  , Env (..)
  , emptyEnv
  , lookupConst
  , addConst
  , constName
  , constLevels
  , constType
  , defPriority
  , isStructureLike
  , ctorOfStructure
  ) where

import qualified Data.IntMap.Strict as IM
import qualified Data.Set        as S
import           Kernel.Expr
import           Kernel.Name

data QuotKind = QType | QCtor | QLift | QInd
  deriving (Eq, Show)

-- | One reduction rule of a recursor: @rec ... (c f1 .. fn) --> rhs@.
data RecRule = RecRule
  { rrCtor      :: !Name
  , rrNumFields :: !Int
  , rrRhs       :: !Expr   -- ^ abstracted over params, motive, minors, fields
  } deriving (Eq, Show)

data IndInfo = IndInfo
  { indName        :: !Name
  , indLevels      :: ![Name]
  , indType        :: !Expr
  , indNumParams   :: !Int
  , indNumIndices  :: !Int
  , indCtors       :: ![Name]     -- ^ in constructor-index order
  , indIsRecursive :: !Bool       -- ^ does some member of the block occur in a field?
  , indLargeElim   :: !Bool       -- ^ may the recursor eliminate into any @Sort@?
  , indK           :: !Bool
    -- ^ does its recursor get K-like reduction?  The same flag as 'recK', kept
    -- here so that a question about a /type/ can be answered without first
    -- finding the recursor that eliminates it; see 'Kernel.Check.proofErasable'.
  } deriving (Eq, Show)

data CtorInfo = CtorInfo
  { ctorName      :: !Name
  , ctorLevels    :: ![Name]
  , ctorType      :: !Expr
  , ctorInduct    :: !Name
  , ctorIdx       :: !Int
  , ctorNumParams :: !Int
  , ctorNumFields :: !Int
  } deriving (Eq, Show)

data RecInfo = RecInfo
  { recName       :: !Name
  , recLevels     :: ![Name]   -- ^ elimination level first under large elimination
  , recType       :: !Expr
  , recInduct     :: !Name     -- ^ the member of the block this one eliminates
  , recNumParams  :: !Int
  , recNumMotives :: !Int      -- ^ one per member of the mutual block
  , recNumIndices :: !Int
  , recNumMinors  :: !Int      -- ^ one per constructor of the /whole/ block
  , recRules      :: ![RecRule]  -- ^ only for 'recInduct'\'s own constructors
  , recK          :: !Bool     -- ^ K-like reduction is available
  } deriving (Eq, Show)

data DefInfo = DefInfo
  { defName   :: !Name
  , defLevels :: ![Name]
  , defType   :: !Expr
  , defValue  :: !Expr
  , defHint   :: !Hint
    -- ^ which of two constants to delta-unfold first; see 'Hint'.
  } deriving (Eq, Show)

-- | Scheduling advice for delta reduction, taken from the export's @hints@
-- field.  Ordered so that the /greater/ of two definitions is the one to unfold
-- first.
--
-- This is the one thing the kernel reads out of the file that it does not
-- check, and it is safe to read precisely because there is nothing to check:
-- the order in which two definitions are unfolded cannot change which terms are
-- convertible.  When neither side wins, 'Kernel.Check.tryDelta' unfolds both, so
-- every ordering -- including a deliberately perverse one -- decides the same
-- questions.  It decides them at very different speeds, and that is all a hint
-- is for.
--
-- @abbrev@ is a definition the elaborator considered too thin to be worth
-- keeping folded, so it goes first.  @regular n@ carries a height: @n@ exceeds
-- the height of everything the value mentions, so unfolding the taller of two
-- constants is what lets the shorter one be reached from both sides.  @opaque@
-- is the elaborator asking for this one to be left alone, and it is also what a
-- theorem gets: the export gives @thm@ no hints field, and a proof is the last
-- thing worth looking inside.
data Hint = HOpaque | HRegular !Int | HAbbrev
  deriving (Eq, Ord, Show)

data ConstInfo
  = CAxiom !Name ![Name] !Expr
  | CDef   !DefInfo
  | CInd   !IndInfo
  | CCtor  !CtorInfo
  | CRec   !RecInfo
  | CQuot  !Name ![Name] !Expr !QuotKind
  deriving (Eq, Show)

constName :: ConstInfo -> Name
constName ci = case ci of
  CAxiom n _ _   -> n
  CDef   d       -> defName d
  CInd   i       -> indName i
  CCtor  c       -> ctorName c
  CRec   r       -> recName r
  CQuot  n _ _ _ -> n

constLevels :: ConstInfo -> [Name]
constLevels ci = case ci of
  CAxiom _ ls _   -> ls
  CDef   d        -> defLevels d
  CInd   i        -> indLevels i
  CCtor  c        -> ctorLevels c
  CRec   r        -> recLevels r
  CQuot  _ ls _ _ -> ls

constType :: ConstInfo -> Expr
constType ci = case ci of
  CAxiom _ _ t   -> t
  CDef   d       -> defType d
  CInd   i       -> indType i
  CCtor  c       -> ctorType c
  CRec   r       -> recType r
  CQuot  _ _ t _ -> t

-- | Which of two definitions to delta-unfold first: the greater goes first.
defPriority :: DefInfo -> Hint
defPriority = defHint

-- | How much the kernel is willing to believe about the arithmetic constants
-- before it computes with them on bignums.  See SPEC.md §6.5.
--
-- The three sound settings differ only in how much evidence they demand; none
-- of them takes a name on trust.  'AccelAlways' does, and exists so that the
-- checker can be made bug-compatible with a kernel that does.
data AccelMode
  = AccelOff        -- ^ never; every operation is unfolded the slow way
  | AccelCanonical  -- ^ only for a declaration matching the stored canonical
                    --   specification exactly (default)
  | AccelVerified   -- ^ for any declaration whose own equations say it computes
                    --   the operation, canonical or not
  | AccelAlways     -- ^ on the strength of the name alone; /unsound/
  deriving (Eq, Show)

-- | Licence questions already answered /yes/ (SPEC.md §6.5).
--
-- Before the kernel computes @2^64 + 1@ on a machine integer it asks whether
-- this file's @Nat.add@ is the operation it thinks it is, and answering means
-- reducing that file's own definitions.  The answer is a property of the
-- environment, and an expensive one -- see 'Kernel.Canon.natProbeArgs' -- so it
-- is asked once and kept.
--
-- Only /positive/ answers are kept, and that is what makes keeping them sound.
-- A licence is established by inspecting the declarations of finitely many
-- named constants, and 'addConst' is write-once: no later declaration can change
-- what those names mean, so a @yes@ stays a @yes@ in every larger environment.
-- A @no@ does not keep -- the constant a dependency needed may simply not have
-- been declared yet -- so a @no@ is forgotten and asked again.
data Licences = Licences
  { licNatShape :: !Bool
    -- ^ @Nat@, @Nat.zero@ and @Nat.succ@ are declared as the kernel expects
  , licStrShape :: !Bool
    -- ^ likewise for the constants a string literal expands through
  , licNatOps   :: !(S.Set Name)
    -- ^ arithmetic operations licensed for acceleration
  , licCanonInd :: !(S.Set Name)
    -- ^ inductive types found to match their stored canonical form
  }

noLicences :: Licences
noLicences = Licences False False S.empty S.empty

data Env = Env
  { envConsts   :: !(IM.IntMap [ConstInfo])
    -- ^ keyed by 'nameHash', with a bucket per hash.  Every reduction step asks
    -- this table what a constant is, and a tree keyed on 'Name' answers with
    -- some seventeen calls to 'compare'; keyed on the hash the same seventeen
    -- steps are primitive integer tests, and only the handful of names in the
    -- surviving bucket are compared properly.  See 'lookupConst'.
  , envQuotInit :: !Bool
  , envAccel    :: !AccelMode
    -- ^ constant for the life of a run; it lives here because the accelerated
    -- reduction rules are part of what the environment means, and because
    -- everything that reduces already has the environment to hand.
  , envUnsafe   :: !(S.Set Name)
    -- ^ constants admitted into the /unsafe fragment/ (SPEC.md §12.7).  They
    -- are ordinary 'CAxiom' entries as far as reduction and typing go -- the
    -- kernel never unfolds one and never derives anything from one -- and this
    -- set is what keeps the safe fragment from mentioning them.  It is
    -- consulted in exactly one place, "Front.Lower"'s barrier check; no rule of
    -- §5 or §6 looks at it, so an unsafe constant behaves as an opaque constant
    -- of its declared type wherever it is legal at all.
  , envLicence  :: !Licences
    -- ^ what has already been established about this environment; a cache, in
    -- the sense that clearing it changes only how long the answer takes.
  }

emptyEnv :: Env
emptyEnv = Env IM.empty False AccelCanonical S.empty noLicences

lookupConst :: Env -> Name -> Maybe ConstInfo
lookupConst env n = IM.lookup (nameHash n) (envConsts env) >>= go
  where
    go (ci : rest) | constName ci == n = Just ci
                   | otherwise         = go rest
    go []                              = Nothing

-- | Declarations are write-once: a repeated name is a hard error, which is what
-- rejects the @dup_*@ tests.
addConst :: Env -> ConstInfo -> Either String Env
addConst env ci
  | Just _ <- lookupConst env n = Left ("duplicate declaration: " ++ showName n)
  | otherwise = Right env
      { envConsts = IM.insertWith (++) (nameHash n) [ci] (envConsts env) }
  where n = constName ci

-- | Eligible for eta and for @Expr.proj@: exactly one constructor, no indices,
-- and not recursive.  (A recursive single-constructor type would make eta
-- expansion diverge.)
isStructureLike :: Env -> Name -> Bool
isStructureLike env n = case lookupConst env n of
  Just (CInd i) -> length (indCtors i) == 1
                && indNumIndices i == 0
                && not (indIsRecursive i)
  _ -> False

ctorOfStructure :: Env -> Name -> Maybe CtorInfo
ctorOfStructure env n = case lookupConst env n of
  Just (CInd i) | [c] <- indCtors i
                , indNumIndices i == 0
                , not (indIsRecursive i)
                , Just (CCtor ci) <- lookupConst env c -> Just ci
  _ -> Nothing
