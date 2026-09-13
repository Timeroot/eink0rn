{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE LambdaCase #-}
-- | Reduction, definitional equality and type inference for the core calculus.
--
-- The rules implemented here are exactly the ones written out in SPEC.md.  If
-- you change one, change the other.
module Kernel.Check
  ( TC
  , TCState (..)
  , runTC
  , runTCLearn
  , throwTC
  -- * The judgements
  , infer
  , checkType
  , inferSortOf
  , assumedSortOf
  , isDefEq
  , whnf
  , whnfCore
  , ensurePi
  , ensureSort
  -- * Helpers used by the inductive module
  , withLocal
  , withLocals
  , freshFVar
  , localType
  , localInfo
  , teleOf
  , closePis
  , closeLams
  , peelSharedParams
  , checkLevel
  , getEnv
  , withEnv
  , setLevelParams
  , expandLit
  , canonIndMatches
  , warmLicences
  ) where

import           Control.Monad          (unless, when)
import           Data.Array.Base        (unsafeRead, unsafeWrite)
import           Data.Bits              ((.&.))
import qualified Data.ByteString.Char8  as B
import           Data.IntMap.Strict     (IntMap)
import qualified Data.IntMap.Strict     as IM
import           Data.IORef             (IORef, modifyIORef', newIORef,
                                         readIORef, writeIORef)
import           Data.List              (find, foldl')
import           Data.Map.Strict        (Map)
import qualified Data.Map.Strict        as M
import           Kernel.Cache           (Budget, Cache, Chain (..), Counter,
                                         Table, bucket, bumpCounter, clearCache,
                                         getFuel, getTable, getWaste, newBudget,
                                         newCache, newCacheBounded, newCounter,
                                         newTable, nextCount, poke, push,
                                         putTable, readCounter, setFuel,
                                         setWaste, tick, writeCounter)
import           Kernel.Canon
import           Kernel.Env
import           Kernel.Expr
import           Kernel.Level
import           Kernel.Name
import           System.IO.Unsafe       (unsafePerformIO)

-- The checking monad ----------------------------------------------------------

-- | Everything one run of the checker carries around.
--
-- Every field is a handle on something mutable, and the record itself never
-- changes: it is built once by 'runTCLearn' and passed down unaltered.  That is
-- what lets 'TC' hand back an answer and nothing else.  A state /threaded/
-- through the monad has to be returned by every action, and the tuple that says
-- so is a heap object at every bind; and the fields that really do change --
-- the innermost local in scope, above all, which every binder replaces -- would
-- be changed by rebuilding this whole record around them.
--
-- The price is that unwinding is no longer free.  With the state threaded, an
-- action that failed carried none back and the caller simply kept its own; now
-- anything that sets a field for the duration of an action has to put it back
-- on the failing path too.  There are four such things -- 'lend', 'speculate',
-- 'withScope' and 'withEnv' -- and each says so where it stands.  Everything
-- else here is either a cache, where a stale write costs nothing, or a supply
-- that only ever goes forwards.  See 'attempt', which is where a failure is
-- most often caught.
data TCState = TCState
  { tcEnv         :: !(IORef Env)
  , tcLocalName   :: !(Table Binder)
  , tcLocalTy     :: !(Table Expr)
                             -- ^ what every local constant made so far stands
                             --   for, in two tables indexed by its identifier:
                             --   the binder it was read from, and its type.
                             --   Mutable, and so not undone by a failing
                             --   speculation -- see 'freshFVar'
  , tcNextFVar    :: !Counter -- ^ the supply of local-constant identifiers; see
                              --   'freshFVar'
  , tcLevelParams :: !(IORef [Name])
                             -- ^ universe parameters the current decl may use
  , tcBudget      :: !Budget   -- ^ the fuel: reduction steps left in the
                               --   current speculation ('unmetered' outside
                               --   one), and the waste: steps still available
                               --   to be spent on speculation.  Mutable, and
                               --   not part of the record, because 'spend'
                               --   touches nothing else and runs on every
                               --   reduction step; see 'Budget'
  , tcCredit      :: !Counter  -- ^ real reduction steps still to be taken
                               --   before the next is added to 'tcWaste'; see
                               --   'wasteRate'
  , tcStarve      :: !Counter  -- ^ how many times reduction has stopped for
                               --   want of budget; see 'starving'
  , tcInferV      :: !Memo     -- ^ memo for 'inferM' @Verify@; see 'Memo'
  , tcInferA      :: !Memo     -- ^ memo for 'inferM' @Assume@
  , tcWhnf        :: !Memo     -- ^ memo for 'whnf'
  , tcDefEq       :: !EqMemo   -- ^ memo for 'isDefEq'; see 'EqMemo'
  , tcCloseIn     :: !Memo     -- ^ memo for 'closeIn'
  , tcInferVC     :: !Memo     -- ^ 'tcInferV' for closed terms; see 'closedMemos'
  , tcInferAC     :: !Memo     -- ^ 'tcInferA' for closed terms
  , tcWhnfC       :: !Memo     -- ^ 'tcWhnf' for closed terms
  , tcDefEqC      :: !EqMemo   -- ^ 'tcDefEq' for closed pairs
  , tcMemoClosed  :: !Bool     -- ^ 'mtClosed': are those four tables of their
                               --   own?  If not they are the four above, and
                               --   'memoClosed' is never asked
  , tcMemoLru     :: !Bool     -- ^ 'mtLru'; see 'memoLookupLru'
  , tcLevelInst   :: !LevelMemo -- ^ memo for 'instLevels'
  , tcLocalId     :: !LocalMemo -- ^ which local stands for which binder; see
                                --   'sharedLocal'
  , tcConsts      :: !ConstMemo -- ^ memo for 'lookupConst' against 'tcEnv'
  , tcScope       :: !Counter  -- ^ the innermost local currently in scope, or
                               --   @-1@; see 'sharedLocal'
  , tcNatOk       :: !(IORef (Maybe Bool))  -- ^ cached 'natShapeOk'; see 'expandLit'
  , tcStrOk       :: !(IORef (Maybe Bool))  -- ^ cached 'strShapeOk'
  , tcNatOps      :: !(IORef (Map Name Bool))  -- ^ cached 'natOpOk'; see 'reduceNatOp'
  , tcCanonOk     :: !(IORef (Map Name Bool))  -- ^ cached 'canonIndMatches'
  , tcSortRes     :: !(IORef (Map Name (Maybe ([Name], Level))))
                             -- ^ cached 'resultUniverse'
  }

-- | Start the four licence caches off from what the environment already knows,
-- and read back what this run added to them.
--
-- Only the @True@ entries travel, in either direction: see 'Licences'.  The
-- caches themselves keep both answers, because within one run a @no@ is worth
-- not asking twice.
seedLicences :: Env -> TCState -> IO ()
seedLicences env s = do
  writeIORef (tcNatOk   s) (if licNatShape l then Just True else Nothing)
  writeIORef (tcStrOk   s) (if licStrShape l then Just True else Nothing)
  writeIORef (tcNatOps  s) (M.fromSet (const True) (licNatOps l))
  writeIORef (tcCanonOk s) (M.fromSet (const True) (licCanonInd l))
  where l = envLicence env

readLicences :: TCState -> IO Licences
readLicences s = do
  nat    <- readIORef (tcNatOk s)
  strv   <- readIORef (tcStrOk s)
  ops    <- readIORef (tcNatOps s)
  canon  <- readIORef (tcCanonOk s)
  pure Licences
    { licNatShape = nat == Just True
    , licStrShape = strv == Just True
    , licNatOps   = yeses ops
    , licCanonInd = yeses canon
    }
  where yeses = M.keysSet . M.filter id

-- | Ask for every licence this environment supports, before anything needs one.
--
-- Nothing here decides anything: each of these questions is asked anyway, the
-- first time reduction meets the operation it is about, and asking early changes
-- only /when/. What it buys is that the answer is then in 'Licences', and so
-- travels to every later declaration instead of being rediscovered by each.
--
-- Which matters when the value checks are deferred ('Front.Lower.Obligation'),
-- because then no value check runs before any other and none of them can hand
-- its licences on. Establishing an arithmetic licence is not cheap -- it
-- type-checks the operation's defining equations, and for @div@ and @mod@ a
-- table of probes -- and on @std@ paying for it once per declaration rather than
-- once per file costs a third of the run.
--
-- Off the caller's budget, since the caller did not ask for this, and behind
-- 'attempt', since a licence that cannot be established is an answer and not a
-- failure.
warmLicences :: TC ()
warmLicences = unmeteredly $ do
  _ <- attempt strShapeOk       -- which needs, and so establishes, 'natShapeOk'
  mapM_ (attempt . natOpOk) natOpNames

-- | A memo table on (term, local environment) pairs.
--
-- Keyed by 'exprHash' and matched by '=='.  Matching on 'ptrEq' alone is
-- tempting -- the tables are asked millions of questions a declaration and a
-- pointer test is one instruction -- but it misses the case that actually
-- repeats.  Reduction /rebuilds/: every beta step substitutes into a body and
-- hands back fresh nodes, so the same subterm arrives at the table again and
-- again as a different pointer with the same shape, and a pointer-matched table
-- answers none of those.  On a machine-generated arithmetic proof that is the
-- difference between a memo and no memo at all: the same handful of stuck
-- comparisons were being recomputed a million times over, each on a freshly
-- rebuilt copy of terms the table already had the answer for.
--
-- Structural equality is affordable here because it is not the naive one.  The
-- bucket is reached by hash, so the two candidates already agree on it; '=='
-- tries 'ptrEq' first and then 'eqE', which is graph-aware -- a plain recursion
-- under a visit budget, with a memoised traversal taking over if the budget runs
-- out -- so a comparison of two shared terms costs their graphs and not their
-- tree unfoldings.
--
-- The second component of the key is the environment the node is read in; see
-- 'envKey'.
--
-- Missing a hit only wastes time.  Buckets are capped so that a hash collision
-- cannot turn the table into a leak.
--
-- The bucket is a chain of entries and not a list of triples, for the reason
-- 'Kernel.Cache.Chain' gives: five words an entry rather than nine, on the
-- tables that are the largest single thing in the heap while a hard declaration
-- is being checked.
type Memo = Cache MemoB

-- | An entry: the term, its environment key, and what the table remembers about
-- it, in one link.
--
-- **The fields are lazy on purpose**, and the two bangs that look free here are
-- the most expensive characters measured in this file.  Every caller of
-- 'memoInsert' has already run the action that produced the value, so the
-- fields are in weak head normal form before the link is built and strictness
-- can force nothing that is not forced: it is, semantically, a no-op.  It is not
-- one for the compiler.  Making them strict makes 'memoInsert' strict, which
-- propagates through 'insertWhnf' and 'insertInfer' into 'whnf' and 'inferM'
-- themselves, and the code GHC then generates for those two allocates
-- **16% more** over a run of @init@ -- 63.93 GB against 55.15 -- and peaks a
-- fifth higher, for the same verdict on every test.
--
-- Bisected one bucket type at a time, and this declaration is the whole of it:
-- with the other four strict and this one lazy the run is 55.15 GB, and with
-- this one strict it is 63.9 to 64.5 whichever way the other four are set.  So
-- they are lazy for uniformity and not for a measurement, having been tried
-- both ways to no effect on either figure.
data MemoB = MNil | MCons Expr {-# UNPACK #-} !Int Expr MemoB

memoEntryKey :: Expr -> Int -> Int
memoEntryKey k ek = hashMix (exprHash k) ek
{-# INLINE memoEntryKey #-}

instance Chain MemoB where
  chainNil = MNil
  chainCap n b0 = if fits n b0 then b0 else trunc n b0
    where
      fits !j b = case b of
        MNil           -> True
        MCons _ _ _ tl -> j > 0 && fits (j - 1 :: Int) tl
      trunc !j b = case b of
        MCons k ek v tl | j > (0 :: Int) -> MCons k ek v (trunc (j - 1) tl)
        _                                -> MNil
  chainHang arr mask = go
    where
      go MNil              !n = pure n
      go (MCons k ek v tl) !n = do
        n' <- go tl n
        let j = memoEntryKey k ek .&. mask
        b <- unsafeRead arr j
        unsafeWrite arr j (MCons k ek v b)
        pure (n' + 1)

memoLookup :: Memo -> Int -> Expr -> IO (Maybe Expr)
memoLookup m ek e = go <$> bucket m (memoEntryKey e ek)
  where
    go (MCons k ek' v rest) | ek == ek', k == e = Just v
                            | otherwise         = go rest
    go MNil                                     = Nothing

-- | 'memoLookup', moving the entry it hits to the front of its bucket.
--
-- What a full bucket forgets is its /last/ link, so the order the links are in
-- is the eviction policy, and 'memoInsert' alone leaves it in insertion order.
-- Under that order an entry the whole declaration shares is evicted by the
-- stream of one-off entries that came after it, which is exactly backwards.
-- Hitting the front link -- which most hits do -- writes nothing.
memoLookupLru :: Memo -> Int -> Expr -> IO (Maybe Expr)
memoLookupLru m ek e = bucket m k >>= \case
  MNil                                     -> pure Nothing
  MCons k0 ek0 v _  | ek0 == ek, k0 == e   -> pure (Just v)
  MCons k0 ek0 v tl                        -> go (MCons k0 ek0 v MNil) tl
  where
    k = memoEntryKey e ek
    go _   MNil = pure Nothing
    go pre (MCons k' ek' v tl)
      | ek' == ek, k' == e = do poke m k (MCons k' ek' v (unwind pre tl))
                                pure (Just v)
      | otherwise          = go (MCons k' ek' v pre) tl
    unwind MNil                rest = rest
    unwind (MCons k' ek' v tl) rest = unwind tl (MCons k' ek' v rest)

memoInsert :: Memo -> Int -> Expr -> Expr -> IO ()
memoInsert m ek k v = push m (memoEntryKey k ek) (MCons k ek v)

-- | Which local constant stands for a binder: the binder's type node and the
-- environment it is read in, to the identifier inference gave it.  See
-- 'sharedLocal'.
type LocalMemo = Cache LocalB

data LocalB = LNil | LCons Expr {-# UNPACK #-} !Int {-# UNPACK #-} !Int LocalB

localEntryKey :: Expr -> Int -> Int
localEntryKey t pk = hashMix (exprHash t) pk
{-# INLINE localEntryKey #-}

instance Chain LocalB where
  chainNil = LNil
  chainCap n b0 = if fits n b0 then b0 else trunc n b0
    where
      fits !j b = case b of
        LNil           -> True
        LCons _ _ _ tl -> j > 0 && fits (j - 1 :: Int) tl
      trunc !j b = case b of
        LCons t pk x tl | j > (0 :: Int) -> LCons t pk x (trunc (j - 1) tl)
        _                                -> LNil
  chainHang arr mask = go
    where
      go LNil               !n = pure n
      go (LCons t pk x tl)  !n = do
        n' <- go tl n
        let j = localEntryKey t pk .&. mask
        b <- unsafeRead arr j
        unsafeWrite arr j (LCons t pk x b)
        pure (n' + 1)

localIdLookup :: LocalMemo -> Int -> Expr -> IO (Maybe Int)
localIdLookup m pk t = go <$> bucket m (localEntryKey t pk)
  where
    go (LCons k pk' x rest) | pk == pk', ptrEq k t = Just x
                            | otherwise            = go rest
    go LNil                                        = Nothing

localIdInsert :: LocalMemo -> Int -> Expr -> Int -> IO ()
localIdInsert m pk t x = push m (localEntryKey t pk) (LCons t pk x)

-- | A memo on /pairs/ of terms: what 'isDefEq' last answered about them.
--
-- Keyed and matched exactly as 'Memo' is, and symmetrically: the key mixes the
-- two hashes in an order that does not depend on which side is which, and a hit
-- accepts the entry either way round.  Conversion is symmetric, so half the
-- questions are the other half asked backwards.
--
-- Sound to consult under any budget, and that is worth spelling out, because a
-- @False@ here is not always the last word.  Every @True@ was produced by the
-- rules of SPEC.md §6 and stays true however much or little reduction preceded
-- it, so replaying one is replaying a proof.  A @False@ can only ever /decline/:
-- it makes a check fail, and a check that fails rejects the file.  So the table
-- can cost completeness and cannot cost soundness -- and to keep the
-- completeness cost at nothing that matters, entries are written only from a
-- call that ran unmetered, never from inside a 'speculate' where @False@ means
-- no more than "not this way".
type EqMemo = Cache EqB

data EqB = ENil | ECons Expr Expr Bool EqB

-- | Symmetric in its arguments, as conversion is.
eqKey :: Expr -> Expr -> Int
eqKey a b = let x = exprHash a; y = exprHash b
            in hashMix (min x y) (max x y)

instance Chain EqB where
  chainNil = ENil
  chainCap n b0 = if fits n b0 then b0 else trunc n b0
    where
      fits !j b = case b of
        ENil           -> True
        ECons _ _ _ tl -> j > 0 && fits (j - 1 :: Int) tl
      trunc !j b = case b of
        ECons x y v tl | j > (0 :: Int) -> ECons x y v (trunc (j - 1) tl)
        _                               -> ENil
  chainHang arr mask = go
    where
      go ENil              !n = pure n
      go (ECons x y v tl)  !n = do
        n' <- go tl n
        let j = eqKey x y .&. mask
        b <- unsafeRead arr j
        unsafeWrite arr j (ECons x y v b)
        pure (n' + 1)

eqLookup :: EqMemo -> Expr -> Expr -> IO (Maybe Bool)
eqLookup m a b = go <$> bucket m (eqKey a b)
  where
    go (ECons x y v rest)
      | x == a && y == b = Just v
      | x == b && y == a = Just v
      | otherwise        = go rest
    go ENil              = Nothing

-- | 'eqLookup' with 'memoLookupLru'\'s eviction order.
eqLookupLru :: EqMemo -> Expr -> Expr -> IO (Maybe Bool)
eqLookupLru m a b = bucket m k >>= \case
  ENil                          -> pure Nothing
  ECons x y v _  | match x y    -> pure (Just v)
  ECons x y v tl                -> go (ECons x y v ENil) tl
  where
    k = eqKey a b
    match x y = (x == a && y == b) || (x == b && y == a)
    go _   ENil = pure Nothing
    go pre (ECons x y v tl)
      | match x y = do poke m k (ECons x y v (unwind pre tl)); pure (Just v)
      | otherwise = go (ECons x y v pre) tl
    unwind ENil             rest = rest
    unwind (ECons x y v tl) rest = unwind tl (ECons x y v rest)

eqInsert :: EqMemo -> Expr -> Expr -> Bool -> IO ()
eqInsert m a b v = push m (eqKey a b) (ECons a b v)

-- | Is a comparison of these two worth a table lookup?
--
-- Anything whose head is not an application or a projection is settled by
-- 'isDefEq'\'s own first line or by one look at a constructor, and remembering
-- that costs more than redoing it.
eqWorthMemo :: Expr -> Expr -> Bool
eqWorthMemo a b = big a && big b
  where big e = case e of App{} -> True; Proj{} -> True; _ -> False

-- | A memo on (stored body, its parameters, universe arguments) triples; see
-- 'instLevels'.
type LevelMemo = Cache LevelB

data LevelB = VNil | VCons Expr [Name] [Level] Expr LevelB

instance Chain LevelB where
  chainNil = VNil
  chainCap n b0 = if fits n b0 then b0 else trunc n b0
    where
      fits !j b = case b of
        VNil             -> True
        VCons _ _ _ _ tl -> j > 0 && fits (j - 1 :: Int) tl
      trunc !j b = case b of
        VCons e ps ls r tl | j > (0 :: Int) -> VCons e ps ls r (trunc (j - 1) tl)
        _                                   -> VNil
  chainHang arr mask = go
    where
      go VNil                 !n = pure n
      go (VCons e ps ls r tl) !n = do
        n' <- go tl n
        let j = levelsKey e ps ls .&. mask
        b <- unsafeRead arr j
        unsafeWrite arr j (VCons e ps ls r b)
        pure (n' + 1)

-- | 'instLevelsE', remembered for the length of one declaration.
--
-- Delta and iota both work by taking a body out of the environment and
-- replacing that declaration's universe parameters with the ones at the
-- occurrence.  A proof that unfolds the same polymorphic constant ten thousand
-- times asks for the same instantiation ten thousand times, and rebuilding the
-- body each time is most of what a large proof costs.
--
-- Keyed the same way as 'Memo': on the body's identity, matched by 'ptrEq'.
-- The bodies come from the environment, so the pointer is stable for as long as
-- the table lives; the universe arguments are compared properly, being short.
-- Missing a hit only wastes time, so the bucket is capped.
--
-- The arguments are part of the /key/ and not only of the entry, which matters
-- more than it sounds: one body instantiated at a dozen different universes is
-- the normal case, not a rare one, and hanging all dozen off the body's hash
-- alone puts them in one bucket, where the cap throws them away as fast as they
-- arrive.
--
-- The /parameters/ are part of it too, and that is not a nicety.  A body is
-- named by its pointer, and two declarations can be handed the same pointer:
-- an exporter files each distinct expression once, so @f.{u,v}@ and @g.{v,u}@
-- with the same body get the same pool index and therefore the same heap
-- object.  Their instantiations at the same @us@ are not the same term -- the
-- lists say which parameter each universe is for -- and an entry that recorded
-- only the body and the arguments would answer for one with the other.  That
-- is not a lost hit but a wrong answer: it makes @f.{0,1}@ and @g.{0,1}@
-- reduce alike and so convertible, which is a universe confusion and unsound.
-- See @tests/bad/level-memo-params.ndjson@, which turns on nothing else.
instLevels :: [Name] -> [Level] -> Expr -> TC Expr
instLevels [] _  e = pure e
instLevels ps ls e
  | sameLength && and (zipWith isSelf ps ls) = pure e
  | otherwise = TC $ \s -> do
      let tbl = tcLevelInst s
          key = levelsKey e ps ls
          hit (VCons b ps' ls' r rest)
            | ptrEq b e, ps' == ps, ls' == ls = Just r
            | otherwise                       = hit rest
          hit VNil                            = Nothing
      b <- bucket tbl key
      case hit b of
        Just r  -> pure (Right r)
        Nothing -> do
          let r = instLevelsE ps ls e
          push tbl key (VCons e ps ls r)
          pure (Right r)
  where
    -- @zipWith@ would otherwise read a short argument list as "every parameter
    -- stands for itself" and hand back a body with the ones it does have left
    -- uninstantiated.  Every caller checks the arity first, so this only closes
    -- the door.
    sameLength = length ps == length ls
    isSelf p (LParam q) = p == q
    isSelf _ _          = False

levelsKey :: Expr -> [Name] -> [Level] -> Int
levelsKey e ps ls = foldl' (\h l -> hashMix h (levelHash l))
                           (foldl' (\h p -> hashMix h (nameHash p)) (exprHash e) ps)
                           ls

-- | A memo on what the environment says about a name; see 'lookupConstC'.
type ConstMemo = Cache ConstB

data ConstB = KNil | KCons Name (Maybe ConstInfo) ConstB

instance Chain ConstB where
  chainNil = KNil
  chainCap n b0 = if fits n b0 then b0 else trunc n b0
    where
      fits !j b = case b of
        KNil         -> True
        KCons _ _ tl -> j > 0 && fits (j - 1 :: Int) tl
      trunc !j b = case b of
        KCons m r tl | j > (0 :: Int) -> KCons m r (trunc (j - 1) tl)
        _                             -> KNil
  chainHang arr mask = go
    where
      go KNil            !n = pure n
      go (KCons m r tl)  !n = do
        n' <- go tl n
        let j = nameHash m .&. mask
        b <- unsafeRead arr j
        unsafeWrite arr j (KCons m r b)
        pure (n' + 1)

-- | 'lookupConst' against the current environment, remembered for as long as
-- that environment is the current one.
--
-- The environment is an 'IntMap' of ninety thousand declarations, so a lookup
-- in it is some seventeen dependent loads, nearly all of them cache misses; and
-- reduction asks it about the head of every application it looks at, sixty-six
-- million times over a run of @std@, almost always about a name it has just
-- asked about.  A direct table indexed by the name's hash answers in one load
-- and a pointer comparison, and costs six per cent of the run's /time/ while
-- allocating essentially nothing.
--
-- What makes it a cache and not a second environment is that it holds no
-- opinion of its own: 'swapEnv' is the only thing that can change what
-- 'lookupConst' would say, and it empties this.  Negative answers are kept for
-- the same reason positive ones are -- within one environment, \"no such
-- constant\" is just as stable a fact.
lookupConstC :: Name -> TC (Maybe ConstInfo)
lookupConstC n = TC $ \s -> do
  let tbl = tcConsts s
      key = nameHash n
      hit (KCons m r rest) | m == n    = Just r
                           | otherwise = hit rest
      hit KNil                         = Nothing
  b <- bucket tbl key
  case hit b of
    Just r  -> pure (Right r)
    Nothing -> do
      env <- readIORef (tcEnv s)
      let r = lookupConst env n
      push tbl key (KCons n r)
      pure (Right r)

-- | The checking monad: failure, and -- because everything the checker
-- remembers is mutable -- 'IO'.  The state is a 'TCState' handed down unchanged
-- rather than threaded, so a bind is a case on an 'Either' and nothing else.
--
-- The 'IO' does not escape.  'runTCLearn' creates the tables, runs the whole
-- computation and returns a value; nothing a caller can hold on to refers to a
-- table, and running the same check twice on the same environment gives the
-- same answer, because a cache is all any of the tables is.  So the outside of
-- 'runTC' is pure, and says so.
newtype TC a = TC { unTC :: TCState -> IO (Either String a) }

instance Functor TC where
  fmap f (TC g) = TC $ \s -> g s >>= \case
    Left e  -> pure (Left e)
    Right a -> pure (Right (f a))

instance Applicative TC where
  pure a = TC $ \_ -> pure (Right a)
  TC f <*> TC g = TC $ \s -> f s >>= \case
    Left e  -> pure (Left e)
    Right h -> g s >>= \case
      Left e  -> pure (Left e)
      Right a -> pure (Right (h a))

instance Monad TC where
  TC g >>= k = TC $ \s -> g s >>= \case
    Left e  -> pure (Left e)
    Right a -> unTC (k a) s

runTC :: Env -> [Name] -> TC a -> Either String a
runTC env lps act = fst <$> runTCLearn env lps act

-- | 'runTC', also handing back the licences established along the way so that
-- the caller can store them in the environment it carries to the next
-- declaration.  See 'Licences' for why that is sound, and 'seedLicences'.
runTCLearn :: Env -> [Name] -> TC a -> Either String (a, Licences)
runTCLearn env lps (TC f) = unsafePerformIO $ do
  inferV  <- newCacheBounded (mtSlots mt)
  inferA  <- newCacheBounded (mtSlots mt)
  whnfM   <- newCacheBounded (mtSlots mt)
  defEq   <- newCacheBounded (mtSlots mt)
  closeM  <- newCacheBounded (mtSlots mt)
  (inferVC, inferAC, whnfC, defEqC) <- closedMemos mt inferV inferA whnfM defEq
  lvlM    <- newCache
  locId   <- newCache
  consts  <- newCache
  credit  <- newCounter wasteRate
  starve  <- newCounter 0
  budget  <- newBudget unmetered wasteBudget
  locNm   <- newTable
  locTy   <- newTable
  nextId  <- newCounter 0
  genv    <- newIORef env
  lvlPs   <- newIORef lps
  scope   <- newCounter (-1)
  natOk   <- newIORef Nothing
  strOk   <- newIORef Nothing
  natOps  <- newIORef M.empty
  canonOk <- newIORef M.empty
  sortRes <- newIORef M.empty
  let s = TCState genv locNm locTy nextId lvlPs budget credit starve
                  inferV inferA whnfM defEq closeM
                  inferVC inferAC whnfC defEqC (mtClosed mt) (mtLru mt)
                  lvlM locId consts scope
                  natOk strOk natOps canonOk sortRes
  seedLicences env s
  r <- f s
  case r of
    Left e  -> pure (Left e)
    Right a -> do lic <- readLicences s
                  pure (Right (a, lic))
  where mt = envMemo env
{-# NOINLINE runTCLearn #-}

throwTC :: String -> TC a
throwTC msg = TC $ \_ -> pure (Left msg)

-- | The four term-keyed memos, over again and unbounded, for closed terms.
--
-- The five of them are bounded ('Kernel.Cache.newCacheBounded') because a
-- remembered answer keeps its question alive, the questions are intermediate
-- terms, and a table that never forgets is a declaration-long root for every one
-- of them.  That is a statement about the /search/, though, and not about the
-- terms worth keeping: those are the ones the declaration reduces over and over,
-- and they are closed, because mentioning a local constant is what reducing
-- under a binder does to a term.  So splitting the tables on 'memoClosed' bounds
-- the half that runs away and lets the half that is shared be bounded by the
-- file instead.
--
-- With 'mtClosed' off both halves are the same four tables and 'memoClosed' is
-- never asked.  'tcCloseIn' is not split: it is keyed on terms with loose bound
-- variables, none of which are closed.
--
-- The three tables left unbounded either way are the three that are not this
-- shape.  'tcLevelInst' is keyed on universe levels, of which a declaration has
-- a handful.  'tcConsts' is keyed on a name and answers with something the
-- environment is holding anyway, so its entries pin nothing.  And 'tcLocalId'
-- is not a cache at all: a miss there does not cost a recomputation, it hands a
-- binder a /second/ local constant, and two locals for one binder is the
-- difference between reading a term's graph and reading its tree unfolding.
closedMemos :: MemoTuning -> Memo -> Memo -> Memo -> EqMemo
            -> IO (Memo, Memo, Memo, EqMemo)
closedMemos mt iv ia wh eq
  | mtClosed mt = (,,,) <$> newCache <*> newCache <*> newCache <*> newCache
  | otherwise   = pure (iv, ia, wh, eq)

-- | Is an answer about this term one for the closed tables?  See 'closedMemos'.
memoClosed :: Expr -> Bool
memoClosed e = not (hasFVars e) && not (hasLooseBVars e)
{-# INLINE memoClosed #-}

-- | Which table a question about this term belongs in, and how to read it.
whnfMemo :: TCState -> Expr -> Memo
whnfMemo s e | tcMemoClosed s, memoClosed e = tcWhnfC s
             | otherwise                    = tcWhnf s
{-# INLINE whnfMemo #-}

inferMemo :: InferMode -> TCState -> Expr -> Memo
inferMemo m s e
  | tcMemoClosed s, memoClosed e = case m of Verify -> tcInferVC s
                                             Assume -> tcInferAC s
  | otherwise                    = case m of Verify -> tcInferV s
                                             Assume -> tcInferA s
{-# INLINE inferMemo #-}

eqMemo :: TCState -> Expr -> Expr -> EqMemo
eqMemo s a b | tcMemoClosed s, memoClosed a, memoClosed b = tcDefEqC s
             | otherwise                                  = tcDefEq s
{-# INLINE eqMemo #-}

memoGet :: TCState -> Memo -> Int -> Expr -> IO (Maybe Expr)
memoGet s | tcMemoLru s = memoLookupLru
          | otherwise   = memoLookup
{-# INLINE memoGet #-}

eqGet :: TCState -> EqMemo -> Expr -> Expr -> IO (Maybe Bool)
eqGet s | tcMemoLru s = eqLookupLru
        | otherwise   = eqLookup
{-# INLINE eqGet #-}

-- Work budgets ------------------------------------------------------------------

-- | The value of 'tcFuel' outside any speculative comparison.
unmetered :: Int
unmetered = maxBound

-- | How much reduction may be /wasted/ on speculation at one go.
--
-- Purely a time/completeness trade-off, with no effect on what counts as a
-- proof: see 'speculate'.  Speculation that pays off is not charged, so this
-- bounds dead ends, not congruence.  Big enough that a comparison needing real
-- but bounded normalisation still gets settled the cheap way; small enough that
-- a few failures cannot run away with an evaluation the caller was about to make
-- unnecessary.
--
-- This is the /burst/: what may be spent before any real work has been done, and
-- the most that may ever be saved up.  See 'wasteRate'.
wasteBudget :: Int
wasteBudget = 50000

-- | Real reduction steps that earn one step of speculation.
--
-- A fixed allowance per declaration is the wrong shape, because declarations are
-- not the same size: a bound generous enough to be invisible on a one-line lemma
-- is spent in the first instant of a machine-generated arithmetic certificate,
-- and what happens then is not that the checker goes slightly slower.  It stops
-- speculating at all, which means it stops taking the cheap way through
-- conversion, and finishes the declaration by brute unfolding -- so the cap
-- meant to stop a proof running away is exactly what makes it run away.
--
-- So the allowance is earned rather than granted: dead ends may consume some
-- fraction of the reduction the checker was going to perform anyway, with
-- 'wasteBudget' as both the opening balance and the ceiling.  Nothing about the
-- calculus depends on the numbers; a starved speculation only ever answers
-- @False@, which means "not this way" and never "not equal".
--
-- The fraction is all of it, and this is not the obvious setting: it was 8 and
-- 8 was a mistake, of exactly the kind the paragraph above describes and did not
-- go far enough about.  Earning slowly does not make a hard declaration slower,
-- it makes it /diverge/, because the allowance and the work are not independent:
-- refusing 'sameHeadCongr' is what sends 'defEqLoop' off to unfold both sides,
-- the unfolding is real reduction, and one step in eight of it comes back as
-- allowance -- which is a feedback loop that settles at a steady state where a
-- fifth of all congruence attempts are refused and the two terms are pulled
-- apart faster than they can be matched.  Measured on the one declaration of
-- @con-leche@ that made the checker run out of a thirteen-gigabyte heap
-- (@ConLeche.Cached.coreKnotI_congr@, all of 1051 nodes):
--
-- @
--   rate 1   ACCEPT   63 MB   13.5s
--   rate 2   ACCEPT   63 MB   12.7s
--   rate 4   ACCEPT   63 MB   13.4s
--   rate 8   does not finish, >20 GB, killed at 900s
-- @
--
-- There is no gradual degradation to read off there and no reason to sit near
-- the edge of it, so the rate is one: a speculation may waste up to as much as
-- the declaration has genuinely spent, and never more than 'wasteBudget' at a
-- go.  Loosening the /other/ number is not a substitute and was measured to be
-- actively harmful -- at a burst of a hundred million a different declaration
-- fails to finish, having spent ten million steps in a single dead end.  The
-- burst is what bounds one bad guess; the rate only decided how often the
-- checker was allowed to guess at all.
wasteRate :: Int
wasteRate = 1

-- | Charge one reduction step.
--
-- A step taken outside a speculation is work the declaration genuinely needed,
-- and earns speculative allowance at the rate 'wasteRate' sets.
spend :: TC ()
spend = TC $ \s -> do
  let b = tcBudget s
  f <- getFuel b
  if f /= unmetered
    then setFuel b (f - 1)
    else do earned <- tick (tcCredit s) wasteRate
            when earned $ do
              w <- getWaste b
              setWaste b (min wasteBudget (w + 1))
  pure (Right ())

-- | Has the current speculative comparison run out of budget?  When it has,
-- reduction stops where it stands and conversion answers @False@.
outOfFuel :: TC Bool
outOfFuel = TC $ \s -> do
  f <- getFuel (tcBudget s)
  let out = f <= 0
  when out (bumpCounter (tcStarve s))
  pure (Right out)

-- | Is this call running outside every speculation?
--
-- 'tcFuel' is 'unmetered' outside one and stays so for the whole call -- 'spend'
-- leaves it alone and 'speculate' puts it back -- so asking once, on entry, is
-- enough.
unmeteredNow :: TC Bool
unmeteredNow = TC $ \s -> do
  f <- getFuel (tcBudget s)
  pure (Right (f == unmetered))

-- | A ticket that says how much reduction has been abandoned half-done.
--
-- 'whnf' remembers what it computed, and what it computes under a speculative
-- budget may not be a normal form: reduction stops where it stands.  Using such
-- a term is harmless -- it is reached from the original by reduction, so it is
-- convertible with it, and a comparison that consults it can fail but cannot
-- wrongly succeed -- but /remembering/ it as the normal form costs a later
-- caller, with a real budget, the answer it was entitled to.
--
-- Rather than refuse to remember anything computed under a budget, take a ticket
-- before and after: if reduction never once stopped for want of fuel, what came
-- back is the normal form, however small the budget was.  That is the common
-- case, and it is the whole value of the memo inside a speculation.
starving :: TC Int
starving = TC $ \s -> do
  n <- readCounter (tcStarve s)
  pure (Right n)

-- | Run a comparison whose /negative/ answer is not conclusive -- the caller
-- will unfold and ask again -- under a budget.
--
-- This is what makes stopping early legitimate.  Every rule that answers
-- @True@ is sound no matter how much reduction preceded it, so a starved
-- comparison can only ever answer @False@, and here @False@ merely means "not
-- this way".  Nothing that is a proof stops being one; a speculation that would
-- have succeeded just costs an unfolding and gets asked again with a fresh
-- budget on the next pass round 'defEqLoop'.
speculate :: TC Bool -> TC Bool
speculate (TC act) = TC $ \s -> do
  let bud = tcBudget s
  fuel0  <- getFuel bud
  waste0 <- getWaste bud
  let allow = if fuel0 == unmetered then waste0 else min fuel0 waste0
  if allow <= 0 then bumpCounter (tcStarve s) >> pure (Right False) else do
     setFuel bud allow
     act s >>= \case
       -- An error raised in here is not the file's error, it is this
       -- comparison's.  With the budget gone, reduction has stopped where it
       -- stands, so a type read off the term it left behind can be anything at
       -- all -- @(fun x => A -> B) c@ is not a function type until someone
       -- affords the beta step -- and the rules that read types off terms have
       -- to be able to say "no opinion" rather than "this file is wrong".  The
       -- caller reads the @False@ as "not this way" and asks again the honest
       -- way.  Nothing is swallowed: every term compared here is a subterm of
       -- something the declaration's own inference visits unmetered, and by
       -- §7.3 a @False@ can only ever decline.
       Left _        -> do setFuel bud fuel0
                           setWaste bud waste0
                           pure (Right False)
       Right b -> do
         fuelEnd  <- getFuel bud
         wasteEnd <- getWaste bud
         let used  = allow - fuelEnd
             fuel' | fuel0 == unmetered = unmetered
                   | otherwise          = max 0 (fuel0 - used)
             -- Only a dead end is charged: work that decided the comparison is
             -- work the checker would have had to do anyway.
             waste' | b         = wasteEnd
                    | otherwise = max 0 (wasteEnd - used)
         setFuel bud fuel'
         setWaste bud waste'
         pure (Right b)

-- | Run an action on a full budget, whatever the caller has left of theirs.
--
-- Only for checks whose answer is cached for a whole environment.  Those must
-- not depend on how much reduction the caller happened to have spent already:
-- a verification starved by an unlucky caller would be remembered as a refusal
-- and switch its rule off for the rest of the file.  The caller's own budget is
-- restored afterwards, so nothing it is entitled to is consumed.
unmeteredly :: TC a -> TC a
unmeteredly act = lend unmetered wasteBudget act

-- | Run an action with the budget set to @(f, w)@ and the caller's put back
-- afterwards, however the action ends.  Restoring it on the failing path too is
-- what the state-passing version did for free: an error carried no state, so
-- what the caller saw was what the caller had.
lend :: Int -> Int -> TC a -> TC a
lend f w (TC act) = TC $ \s -> do
  let bud = tcBudget s
  fuel0  <- getFuel bud
  waste0 <- getWaste bud
  setFuel bud f
  setWaste bud w
  r <- act s
  setFuel bud fuel0
  setWaste bud waste0
  pure r

-- | Run an action on a fixed budget, whatever the caller has left of theirs.
--
-- 'unmeteredly' is right for a check that reduces /open/ terms: those get stuck
-- quickly, and a full budget is what makes the answer a property of the
-- environment.  A check that reduces /closed/ terms has no such guarantee -- a
-- definition by well-founded recursion, handed a numeral, can unfold its
-- accessibility proof for as long as there is memory -- so the probes of
-- 'nocProbes' get a budget of their own.  It is a fixed one, so the answer is
-- still a property of the environment and not of the caller; and a starved probe
-- answers @False@, which only ever declines a shortcut.
onBudget :: Int -> TC a -> TC a
onBudget n = lend n n

-- | What the whole probe battery of one operation may spend.
--
-- Generous next to what a faithful export needs -- the largest probe is a
-- division of a two-digit numeral -- and small enough that a definition which
-- does not compute cannot turn the attempt into the checker's whole afternoon.
probeBudget :: Int
probeBudget = 5000000

-- | Skip a rule that has to infer a type.  With no budget left reduction has
-- stopped where it stands, so the types it would read off are not the real
-- ones; the honest answer is "no opinion".
withFuel :: TC (Maybe a) -> TC (Maybe a)
withFuel act = outOfFuel >>= \out -> if out then pure Nothing else act

getEnv :: TC Env
getEnv = TC $ \s -> Right <$> readIORef (tcEnv s)

setLevelParams :: [Name] -> TC ()
setLevelParams lps = TC $ \s -> do
  forgetMemos s
  writeIORef (tcLevelParams s) lps
  pure (Right ())

-- | Introduce a local constant: an identifier no other local has had, and an
-- entry saying what it stands for.
--
-- Both live outside the checker's state, which is not only cheaper -- a local is
-- made at every binder inference reads, and rebuilding the state record for it
-- was most of what reading a binder cost -- but also the honest reading of
-- \"fresh\".  A speculative comparison that fails is unwound by handing the
-- caller its own state back, and unwinding a /counter/ would hand the next
-- binder an identifier that a local made during the speculation already has.
-- Nothing that outlives the speculation should be able to name that local, but
-- 'tcLocalId' can: it is a table, and a table is not unwound either.  So the
-- supply only ever goes up, and the local tables only ever grow; an entry for a
-- local nothing can reach again is so much dead weight, and dead weight is all
-- it is.
--
-- Which is why those tables are 'Table's and not maps: the identifiers are
-- consecutive, so the entry for one can be a slot in an array rather than a
-- node in a tree, and the millions of them a hard declaration makes then cost
-- two words each rather than the two dozen a tree charges for the path it
-- copies on the way down.
freshFVar :: Binder -> Expr -> TC Int
freshFVar n t = TC $ \s -> do
  i <- nextCount (tcNextFVar s)
  putTable (tcLocalName s) i n
  putTable (tcLocalTy s) i t
  pure (Right i)

-- | The type a local constant was introduced with.
localType :: Int -> TC Expr
localType i = TC $ \s -> readLocal s i (getTable (tcLocalTy s) i)

-- | The binder name and type a local constant was introduced with.
localInfo :: Int -> TC (Binder, Expr)
localInfo i = TC $ \s -> readLocal s i $
  (,) <$> getTable (tcLocalName s) i <*> getTable (tcLocalTy s) i

-- | Read something about local constant @i@, having first made sure there is
-- one.  The tables are unchecked, so this bounds check is the whole of what
-- stands between a malformed term and a read past the end of an array; the
-- supply says exactly how many locals have been made.
readLocal :: TCState -> Int -> IO a -> IO (Either String a)
readLocal s i act = do
  n <- readCounter (tcNextFVar s)
  if i >= 0 && i < n then Right <$> act
                     else pure (Left ("unbound local constant x!" ++ show i))
{-# INLINE readLocal #-}

-- | Run an action against a temporarily different environment.  Local
-- constants are unaffected: they are indexed by a counter that only ever grows,
-- so a local made under one environment stays valid under another.
--
-- Put back on the failing path too, as 'lend' is and for the same reason: an
-- error no longer carries the caller's state back with it.
withEnv :: Env -> TC a -> TC a
withEnv env (TC act) = TC $ \s -> do
  old <- readIORef (tcEnv s)
  swapEnv env s
  r <- act s
  swapEnv old s
  pure r

-- | Install an environment, throwing away everything that was an answer about
-- the old one.
--
-- The inference and whnf memos are keyed on the term alone, so anything the
-- answer also depends on -- the environment a constant unfolds in, the
-- declaration's universe parameters -- has to invalidate them.  The licence
-- answers are about the environment rather than about a term, so they are not
-- thrown away but re-seeded from the incoming one: see 'seedLicences'.
--
-- 'tcLevelInst' survives untouched, because what it remembers is a pure
-- function of its key: substituting universes in a term does not consult the
-- environment at all.
swapEnv :: Env -> TCState -> IO ()
swapEnv env s = do
  forgetMemos s
  clearCache (tcConsts s)
  writeIORef (tcEnv s) env
  seedLicences env s

-- | Throw away everything keyed on a term alone.  'tcLevelInst' and 'tcCloseIn'
-- are not among them: what they remember is a pure function of the key, and
-- neither is
-- 'tcLocalId': what it remembers is which /name/ a binder was given, and a name
-- means the same thing under every environment.  'tcConsts' is not either, but
-- for the opposite reason -- it is about the environment and nothing else, so
-- 'swapEnv' empties it and a change of universe parameters leaves it alone.
forgetMemos :: TCState -> IO ()
forgetMemos s = do
  clearCache (tcInferV s)
  clearCache (tcInferA s)
  clearCache (tcWhnf s)
  clearCache (tcDefEq s)
  when (tcMemoClosed s) $ do
    clearCache (tcInferVC s)
    clearCache (tcInferAC s)
    clearCache (tcWhnfC s)
    clearCache (tcDefEqC s)

-- | Run an action with @x@ recorded as the innermost local in scope.
--
-- 'tcScope' is not a context -- 'tcLocalTy' is -- but a token for one: what it
-- identifies is the whole chain of locals a term may mention free.  See
-- 'sharedLocal', which is the only thing that reads it.
--
-- Put back on the failing path too, as 'lend' is and for the same reason.
withScope :: Int -> TC a -> TC a
withScope x (TC act) = TC $ \s -> do
  let sc = tcScope s
  old <- readCounter sc
  writeCounter sc x
  r <- act s
  writeCounter sc old
  pure r

-- | Introduce a local constant of the given type and run an action with it.
withLocal :: Binder -> Expr -> (Int -> TC a) -> TC a
withLocal n t k = freshFVar n t >>= \x -> withScope x (k x)

-- | The local constant that stands for a binder.  @raw@ is the binder's type as
-- it appears in the term, still open with respect to @env@; the continuation
-- also gets it closed.
--
-- The point is that two readings of the /same/ binder node in the /same/ scope
-- get the /same/ local, where 'withLocal' would have given them two.  That
-- sounds like a nicety and is the difference between checking a shared term and
-- checking the tree it denotes.  Inference is memoised on the pair of a node and
-- the environment it is read in ('memoKey'), and an environment is identified by
-- its innermost local ('envKey'); so if every binder hands out a brand new
-- local, a subterm reached along @2^n@ paths is read in @2^n@ environments no
-- two of which are ever the same, the memo never answers, and the checker walks
-- the term's tree unfolding.  Handing out the same local along every path
-- collapses those environments back into one.
--
-- A local is only a name, and the type this one is recorded with is
-- @closeIn env raw@ -- a function of exactly what the entry is keyed on, since
-- the scope determines the environment.  So two binders that share a local do
-- agree about what it is.
--
-- What must not happen is for a binder to be given a local that some enclosing
-- binder already holds, because then 'abstractFVars' would capture the wrong
-- occurrences.  It cannot: a local is created fresh and filed under one key,
-- so if a lookup in scope @p@ returned a local @x@ that is already somewhere in
-- @p@'s own chain, @x@ would have been filed under a scope that is a descendant
-- of @x@ -- and a descendant of @x@ is something that did not exist when @x@ was
-- made.
sharedLocal :: LEnv -> Binder -> Expr -> (Int -> Expr -> TC a) -> TC a
sharedLocal env n raw k = do
  p     <- currentScope
  found <- TC $ \s -> Right <$> localIdLookup (tcLocalId s) p raw
  case found of
    Just x  -> do (_, t') <- localInfo x
                  withScope x (k x t')
    Nothing -> do
      t' <- closeIn env raw
      x  <- freshFVar n t'
      TC $ \s -> Right <$> localIdInsert (tcLocalId s) p raw x
      withScope x (k x t')

-- | The innermost local in scope; see 'withScope'.
currentScope :: TC Int
currentScope = TC $ \s -> Right <$> readCounter (tcScope s)

-- | Open a telescope, introducing one local per binder.  The telescope's types
-- are in de Bruijn form relative to the preceding binders.
withLocals :: [(Binder, Expr)] -> ([Int] -> TC a) -> TC a
withLocals tele k = go [] tele
  where
    go acc []            = k (reverse acc)
    go acc ((n, t) : ts) = do
      let t' = instN (map FVar acc) t
      x <- freshFVar n t'
      withScope x (go (x : acc) ts)

-- | Recover a closed de Bruijn telescope from locals introduced in order.
teleOf :: [Int] -> TC [(Binder, Expr)]
teleOf xs = mapM one (zip [0 ..] xs)
  where
    one (i, x) = do
      (n, t) <- localInfo x
      pure (n, abstractFVars (take i xs) t)

-- | Close a term over locals introduced in order, as a @Pi@ or @Lam@ telescope.
closePis, closeLams :: [Int] -> Expr -> TC Expr
closePis  = closeWith Pi
closeLams = closeWith Lam

closeWith :: (Binder -> Expr -> Expr -> Expr) -> [Int] -> Expr -> TC Expr
closeWith mk xs body = do
  tele <- teleOf xs
  pure (foldr (\(n, t) acc -> mk n t acc) (abstractFVars xs body) tele)

-- | Peel the shared parameter telescope off an arity or a constructor type,
-- substituting the given parameter locals for it and requiring the binder types
-- to agree.
peelSharedParams :: String -> Int -> [Int] -> Expr -> TC Expr
peelSharedParams ctxt nps = go nps
  where
    go 0 _ ty = pure ty
    go k (p : rest) ty = whnf ty >>= \case
      Pi _ dom cod -> do
        pt <- localType p
        ok <- isDefEq dom pt
        unless ok $
          throwTC (ctxt ++ "parameter " ++ show (nps - k) ++ " has the wrong type")
        go (k - 1) rest (inst1 (FVar p) cod)
      _ -> throwTC (ctxt ++ "expected " ++ show nps ++ " parameter binders")
    go _ [] _ = throwTC (ctxt ++ "parameter list exhausted")

-- | Every universe parameter mentioned must have been declared.
checkLevel :: Level -> TC ()
checkLevel l = TC $ \s -> do
  lps <- readIORef (tcLevelParams s)
  pure $ case [ p | p <- levelParamsOf l, p `notElem` lps ] of
    []      -> Right ()
    (p : _) -> Left ("undeclared universe parameter " ++ showName p)

-- Weak head normalisation -----------------------------------------------------

-- | Full weak head normal form: 'whnfCore' interleaved with delta unfolding.
--
-- Memoised on the node, for the reason 'inferM' is: a term is a graph, and a
-- subterm reachable along many paths would otherwise be normalised once per
-- path.  That is the whole cost of evaluating an arithmetic proof, where the
-- same instance -- @instHMul@, @instOfNat@ -- is reached from every operation
-- in the expression.
--
-- The entry is recorded only outside a speculation.  A starved reduction stops
-- where it stands and returns a term that is correct to /use/ -- 'speculate'
-- reads a failure to reduce as "not this way", never as "not equal" -- but not
-- correct to remember, since a later caller with a real budget would be handed
-- the half-reduced term as if it were the normal form and could fail a
-- comparison that holds.  Outside a speculation 'tcFuel' is 'unmetered' and
-- stays so for the whole call: 'spend' leaves it alone and 'speculate' puts it
-- back, so testing it once, on entry, is enough.
--
-- 'tcWaste', which a nested speculation can exhaust, needs no guard: it only
-- decreases within a declaration and resets between them, so the first
-- encounter with a node is the one with the most budget and no later caller is
-- handed a result computed with less than it had itself.  The other direction
-- is not a hazard -- a result reduced further than the caller could have
-- managed is still reached by reduction steps.
whnf :: Expr -> TC Expr
whnf e
  | not (reducible e) = whnfRaw e
  | otherwise         = lookupWhnf e >>= \case
      Just v  -> pure v
      Nothing -> do
        before <- starving
        v      <- whnfRaw e
        after  <- starving
        when (before == after) (insertWhnf e v)
        pure v
  where
    -- A head that no rule applies to is its own normal form, and looking that
    -- up costs more than rediscovering it.
    --
    -- The test is on the node and not on 'headOf ex', which would catch far
    -- more: a spine headed by a local or a free variable is its own normal form
    -- too, and those are most of the terms there are.  Measured twice, it costs
    -- 8% more allocation and 2% more time to catch them, and the reason is the
    -- two tickets above.  Short-circuiting means 'whnfCore' and 'unfoldDelta'
    -- never read the budget, so they never bump 'tcStarve', so a great many
    -- results computed part-way through an exhausted speculation now look like
    -- normal forms and get recorded.  Recording them is not wrong -- they are
    -- reached by reduction, and 'speculate' can only answer @False@ -- but the
    -- entries cost more than the lookups they save.
    reducible ex = case ex of
      App{} -> True; Const{} -> True; Let{} -> True; Proj{} -> True
      _     -> False

whnfRaw :: Expr -> TC Expr
whnfRaw e = do
  e1 <- whnfCore e
  unfoldDelta e1 >>= \case
    Just e2 -> whnf e2
    Nothing -> pure e1

lookupWhnf :: Expr -> TC (Maybe Expr)
lookupWhnf e = TC $ \s -> do
  v <- memoGet s (whnfMemo s e) whnfKey e
  pure (Right v)

insertWhnf :: Expr -> Expr -> TC ()
insertWhnf k v = TC $ \s -> do
  memoInsert (whnfMemo s k) whnfKey k v
  pure (Right ())

-- | 'whnf' takes no 'LEnv' -- it is only ever called on closed terms, since the
-- types inference hands out are closed -- so the environment half of the key is
-- the same for every entry.
whnfKey :: Int
whnfKey = envKey []

-- | Everything except delta: beta, zeta, iota (recursors and @Quot@), and
-- projection reduction.
--
-- The head is found with 'headOf' rather than by 'unApps', and the spine is
-- built only in the branches that need it.  Most calls reach a head no rule
-- applies to -- a local constant, an axiom, a constructor, an inductive type --
-- and taking such a term apart to discover that costs a cons cell per argument
-- and rebuilds nothing.
whnfCore :: Expr -> TC Expr
whnfCore = go
  where
    go e = outOfFuel >>= \out -> if out then pure e else case headOf e of
      h@Lam{}     -> case e of
        App{}    -> step (betaApply h (argsOf e))
        _        -> pure e
      Let _ _ v b -> step (mkApps (inst1 v b) (argsOf e))
      h@Proj{}    -> reduceProj h >>= \case
        Just h'  -> step (mkApps h' (argsOf e))
        Nothing  -> pure e
      Const n ls  -> reduceConstApp e n ls >>= \case
        Just e'  -> step e'
        Nothing  -> pure e
      _           -> pure e
    step e = spend >> go e

-- | The arguments of a spine, for a caller that already has its head.
argsOf :: Expr -> [Expr]
argsOf = snd . unApps

-- | Beta: peel as many leading lambdas as there are arguments and substitute
-- them all at once.  The accumulator ends up in exactly the order 'instN'
-- wants, innermost binder first.
betaApply :: Expr -> [Expr] -> Expr
betaApply = go []
  where
    go acc (Lam _ _ b) (a : as) = go (a : acc) b as
    go acc body        args     = mkApps (instN acc body) args

-- | Unfold the head constant if it is a definition.
--
-- Spine built only once the head is known to be one; see 'whnfCore'.
unfoldDelta :: Expr -> TC (Maybe Expr)
unfoldDelta e = outOfFuel >>= \out -> if out then pure Nothing else
  case headOf e of
    Const n ls -> lookupConstC n >>= \case
        Just (CDef d) | length ls == length (defLevels d) -> do
          let args = argsOf e
          held <- natBlocked n args
          if held then pure Nothing else do
            spend
            body <- instLevels (defLevels d) ls (defValue d)
            pure (Just (betaApply body args))
        _ -> pure Nothing
    _ -> pure Nothing

-- | Iota for recursors and for @Quot.lift@ / @Quot.ind@, plus arithmetic on
-- numerals.
--
-- Takes the whole application rather than its spine, so that a head no rule
-- fires on -- which is most of them -- costs one environment lookup and nothing
-- else.
reduceConstApp :: Expr -> Name -> [Level] -> TC (Maybe Expr)
reduceConstApp e n ls = lookupConstC n >>= \case
    Just (CRec r)            -> reduceRec r ls (argsOf e)
    Just (CQuot _ _ _ QLift) -> reduceQuot 6 5 3 (argsOf e)
    Just (CQuot _ _ _ QInd)  -> reduceQuot 5 4 3 (argsOf e)
    -- No guard on the kind of constant: what licenses the shortcut is
    -- 'natOpOk', and an operation that is not a definition cannot satisfy the
    -- equations it asks about.  Leaving the kind out of it is what makes
    -- 'AccelAlways' the honest name for a mode that trusts the name alone.
    Just _ | Just op <- lookupNatOp n -> reduceNatOp n op (argsOf e)
    _                        -> pure Nothing

-- | @Quot.lift a r b f h (Quot.mk a r v) --> f v@ (and likewise @Quot.ind@).
--
-- @arity@ is the number of arguments the eliminator takes, @majorIx@ the
-- position of the quotient argument and @fnIx@ the position of the function.
reduceQuot :: Int -> Int -> Int -> [Expr] -> TC (Maybe Expr)
reduceQuot arity majorIx fnIx args
  | length args < arity = pure Nothing
  | otherwise = do
      major <- whnf (args !! majorIx)
      let (mh, margs) = unApps major
      case mh of
        Const cn _ -> lookupConstC cn >>= \case
          Just (CQuot _ _ _ QCtor) | length margs == 3 ->
            pure (Just (mkApps (App (args !! fnIx) (margs !! 2)) (drop arity args)))
          _ -> pure Nothing
        _ -> pure Nothing

-- | @T.rec params motives minors indices (c params fields) --> rule_c params motives minors fields@
--
-- A mutual block shares one set of motives and one set of minor premises across
-- all its members, so the prefix a rule is applied to is the same for every
-- recursor in the block; only the rules themselves differ.
reduceRec :: RecInfo -> [Level] -> [Expr] -> TC (Maybe Expr)
reduceRec r ls args
  | length ls /= length (recLevels r) = pure Nothing
  | length args <= majorIx            = pure Nothing
  | otherwise = do
      major0 <- whnf (args !! majorIx)
      mmajor <- toCtorApp r ls major0
      case mmajor of
        Nothing    -> pure Nothing
        Just major -> do
          let (mh, margs) = unApps major
          case mh of
            Const cn _ | Just rule <- find ((== cn) . rrCtor) (recRules r)
                       , length margs >= rrNumFields rule -> do
              rhs <- instLevels (recLevels r) ls (rrRhs rule)
              let fields = drop (length margs - rrNumFields rule) margs
                  before = take prefixLen args
                  after  = drop (majorIx + 1) args
              pure (Just (mkApps (mkApps rhs (before ++ fields)) after))
            _ -> pure Nothing
  where
    prefixLen = recNumParams r + recNumMotives r + recNumMinors r
    majorIx   = prefixLen + recNumIndices r

-- | Try to see the major premise as a constructor application.  Beyond the
-- literal case this is where K-like reduction and structure eta live.
toCtorApp :: RecInfo -> [Level] -> Expr -> TC (Maybe Expr)
toCtorApp r ls major = do
  m1 <- expandLit major
  case headOf m1 of
    Const cn _ -> lookupConstC cn >>= \case
      Just (CCtor _) -> pure (Just m1)
      _              -> notACtor m1
    _ -> notACtor m1
  where
    notACtor m1 | recK r    = toCtorWhenK r ls m1
                | otherwise = toCtorWhenStruct r m1

-- | K-like reduction.  Only for a @Prop@ with a single field-less constructor:
-- if the major premise's type is @T params indices@ then the /canonical/
-- constructor application has that same type, so we may replace the (possibly
-- neutral) major premise by it.
--
-- The @isDefEq@ guard below is essential: without it @Eq.rec@ would reduce at
-- @Eq a b@ for @a@ and @b@ that are not convertible.
toCtorWhenK :: RecInfo -> [Level] -> Expr -> TC (Maybe Expr)
toCtorWhenK r _ls major = withFuel $ do
  majorTy <- inferOnly major >>= whnf
  let (h, targs) = unApps majorTy
  case h of
    Const tn tls | tn == recInduct r -> lookupConstC tn >>= \case
      Just (CInd ind)
        | [cn] <- indCtors ind
        , length targs >= indNumParams ind -> lookupConstC cn >>= \case
            Just (CCtor ci) | ctorNumFields ci == 0 -> do
              let ctorApp = mkApps (Const cn tls) (take (indNumParams ind) targs)
              ctorTy <- inferOnly ctorApp
              ok <- isDefEq majorTy ctorTy
              pure (if ok then Just ctorApp else Nothing)
            _ -> pure Nothing
      _ -> pure Nothing
    _ -> pure Nothing

-- | Structure eta on the major premise: for a structure-like @T@ every element
-- is convertible to @T.mk s.0 .. s.(n-1)@.
--
-- Only for a /non-recursive/ structure: see 'isEtaReducible'.
toCtorWhenStruct :: RecInfo -> Expr -> TC (Maybe Expr)
toCtorWhenStruct r major = withFuel $ do
  env <- getEnv
  lookupConstC (recInduct r) >>= \case
    Just (CInd ind)
      | isEtaReducible env (indName ind)
      , [cn] <- indCtors ind -> lookupConstC cn >>= \case
          Just (CCtor ci) -> do
            majorTy <- inferOnly major >>= whnf
            let (h, targs) = unApps majorTy
            case h of
              Const tn tls | tn == indName ind, length targs == indNumParams ind ->
                pure . Just $ mkApps (Const cn tls)
                  (targs ++ [ Proj tn i major | i <- [0 .. ctorNumFields ci - 1] ])
              _ -> pure Nothing
          _ -> pure Nothing
    _ -> pure Nothing

-- | @(T.mk params fields).i --> fields !! i@
reduceProj :: Expr -> TC (Maybe Expr)
reduceProj (Proj tn i s) = do
  s1 <- whnf s >>= expandLit
  let (h, args) = unApps s1
  case h of
    Const cn _ -> lookupConstC cn >>= \case
      Just (CCtor ci)
        | ctorInduct ci == tn
        , let fields = drop (ctorNumParams ci) args
        , i < length fields -> pure (Just (fields !! i))
      _ -> pure Nothing
    _ -> pure Nothing
reduceProj _ = pure Nothing

-- | Unfold a literal one step into constructor form, when something needs to
-- see a constructor.  @NatLit@ and @StrLit@ are abbreviations, nothing more.
--
-- The catch is that the abbreviation is written in terms of /names/ -- @Nat.succ@,
-- @String.mk@ and so on -- and a name is not evidence.  Expanding unconditionally
-- would hand the file a definitional equality it never justified: declare
-- @Nat.succ@ with some other argument type and iota on @nat_lit 1@ produces a
-- minor premise applied to an argument of the wrong type.  It is the same trust
-- violation as computing @Nat.add@ on bignums because of what it is called; see
-- the arithmetic section below, where that licence is earned rather than assumed.
--
-- So the constants a literal denotes are checked to be the ones it means, and a
-- literal over constants that are not simply does not reduce.  It keeps its type
-- and stays opaque, which is sound: an uninterpreted constant proves nothing.
-- The answers are cached per environment, since a literal-heavy file asks
-- constantly and the shapes cannot change under it.
expandLit :: Expr -> TC Expr
expandLit e@(NatLit n)
  | n < 0     = pure e
  | otherwise = natShapeOk >>= \ok -> pure $ if not ok then e else
      if n == 0 then Const nameNatZero []
                else App (Const nameNatSucc []) (NatLit (n - 1))
expandLit e@(StrLit s) =
  strShapeOk >>= \ok -> pure (if not ok then e else stringOf (utf8Chars s))
expandLit e = pure e

-- | The string whose characters are these code points, in constructor form.
--
-- A @String@ is not a list of characters but the /byte array a list of
-- characters encodes/, together with the evidence that it is such an encoding:
--
-- > structure String where
-- >   ofByteArray ::
-- >   toByteArray : ByteArray
-- >   isValidUTF8 : ByteArray.IsValidUTF8 toByteArray
-- >
-- > inductive ByteArray.IsValidUTF8 (b : ByteArray) where
-- >   | intro (m : List Char) (hm : b = List.utf8Encode m)
--
-- So the literal's meaning is written by handing @List.utf8Encode@ the character
-- list and taking the evidence from the character list itself, where the equation
-- the constructor asks for holds by reflexivity.  The result is well typed
-- whatever @List.utf8Encode@ happens to compute, which is the point: the kernel
-- says what a literal /is/, not what its bytes are, and leaves the encoding to
-- the file that defined it.
stringOf :: [Integer] -> Expr
stringOf cps = mkApps (Const nameStringOfByteArray []) [bytes, valid]
  where
    char  = Const nameChar []
    chars = foldr (\c acc -> mkApps (Const nameListCons [LZero])
                                    [char, App (Const nameCharOfNat []) (NatLit c), acc])
                  (App (Const nameListNil [LZero]) char)
                  cps
    bytes = App (Const nameUtf8Encode []) chars
    valid = mkApps (Const nameValidUtf8Intro [])
                   [ bytes, chars
                   , mkApps (Const nameEqRefl [LSucc LZero])
                            [Const nameByteArray [], bytes] ]

-- | @Nat@ really is an inductive type whose @zero@ and @succ@ are constructors
-- of the shape a numeral is spelt in.
--
-- The field /types/ are not spelt out here; instead a canonical expansion is
-- type-checked, which pins them without anyone having to write a de Bruijn term
-- by hand.  One witness suffices because every numeral's expansion has this same
-- shape -- @Nat.succ@ applied to a numeral -- and differs only in the numeral.
natShapeOk :: TC Bool
natShapeOk = cached tcNatOk $ do
  env <- getEnv
  if not (all (isCtorOf env nameNat) [(nameNatZero, 0, 0), (nameNatSucc, 0, 1)])
    then pure False
    else wellTyped (App (Const nameNatSucc []) (NatLit 0)) (Const nameNat [])

-- | @String@ really is the byte-array-plus-evidence structure 'stringOf' builds,
-- and the pieces a string literal is spelt with fit together.
--
-- Again one witness does it: a one-character string exercises every constant of
-- the expansion -- @String.ofByteArray@, @ByteArray.IsValidUTF8.intro@,
-- @List.utf8Encode@, @Eq.refl@, @List.cons@, @List.nil@, @Char.ofNat@ -- at
-- exactly the types any longer string uses them at, since strings differ only in
-- the length of the character list and the numerals in it.
--
-- Only @String.ofByteArray@, @List.nil@ and @List.cons@ are /required/ to be
-- constructors, and for the same reason: an expansion whose head is not one is
-- inert, so nothing that wanted to see a constructor gets to see the wrong thing.
-- The rest may be anything of the right type; the witness pins that much, and no
-- rule below reads them.  In particular the kernel does not check what
-- @List.utf8Encode@ computes -- it need not, because the evidence field is
-- 'stringOf'\'s own @Eq.refl@ and the field is a proof, so nothing downstream can
-- depend on the answer being UTF-8.
strShapeOk :: TC Bool
strShapeOk = cached tcStrOk $ do
  env <- getEnv
  n <- natShapeOk
  if not n || not (isCtorOf env nameString (nameStringOfByteArray, 0, 2))
             || not (all (isCtorOf env nameList) [(nameListNil, 1, 0), (nameListCons, 1, 2)])
    then pure False
    else wellTyped (stringOf [0]) (Const nameString [])

-- Arithmetic on numerals ---------------------------------------------------------
--
-- @Nat.ble 1114113 4294967296@ is a single machine comparison and about a
-- million iota steps.  A kernel that only knows the second reading cannot check
-- @Init.Prelude@, where bounds like @UInt32.size@ are settled by @decide@; so
-- the numerals have to be computed on, not just unfolded.
--
-- The danger is precisely the one 'expandLit' guards against.  @Nat.add@ is a
-- name, and a file that defines it as, say, multiplication would be handed an
-- equation the theory does not contain -- @2 + 2 ≡ 5@ if the kernel is willing
-- to say so on the strength of the name alone.  Every soundness bug of this
-- shape has the same cause: a constant the kernel gives a meaning to without
-- checking that the file gave it the same one.
--
-- So the shortcut is not taken on trust; it is /derived/, once per environment,
-- from the definition's own defining equations.  For @Nat.add@ the kernel checks
--
-- > add x 0       ≡ x                            (x, y fresh locals of type Nat)
-- > add x (succ y) ≡ succ (add x y)
--
-- and nothing else.  Both are ordinary conversion questions about open terms,
-- and conversion is stable under substitution, so they may be instantiated at
-- any closed terms.  That is enough to settle every numeral case at the meta
-- level, by induction on @b@:
--
-- >   add ⌜a⌝ ⌜0⌝       ≡ add ⌜a⌝ 0            (natShapeOk)
-- >                     ≡ ⌜a⌝                   (first equation at x := ⌜a⌝)
-- >   add ⌜a⌝ ⌜k+1⌝     ≡ add ⌜a⌝ (succ ⌜k⌝)   (natShapeOk)
-- >                     ≡ succ (add ⌜a⌝ ⌜k⌝)   (second equation)
-- >                     ≡ succ ⌜a+k⌝           (induction hypothesis)
-- >                     ≡ ⌜a+k+1⌝              (natShapeOk)
--
-- so @add ⌜a⌝ ⌜b⌝ ≡ ⌜a+b⌝@ for all @a@ and @b@, which is exactly what the
-- shortcut asserts.  The other operations go the same way; those whose equations
-- are stated in terms of another operation (@sub@ via @pred@, @mul@ via @add@,
-- @pow@ via @mul@) additionally need that one verified, since the induction step
-- appeals to its numeral case.
--
-- Two properties make this safe rather than merely plausible.  The equations are
-- written with the very constants the shortcut will emit -- @Nat.succ@,
-- @Nat.zero@, @Bool.true@ -- so whatever those names happen to denote, the
-- induction concludes something about the term actually produced; no name is
-- believed, only related to itself.  And failure is inert: an operation whose
-- equations do not check simply is not accelerated, and reduces the slow way.
--
-- The equations do not, on their own, say the operation has the right /type/.
-- They are conversion questions, and conversion does not typecheck what it is
-- given; an @Nat.add@ declared at @Foo -> Foo -> Foo@ whose equations somehow
-- went through would have the kernel replace a term of type @Foo@ with a
-- numeral.  So the declared type is compared against the stored one too, in
-- every mode that checks anything.
--
-- On top of that, 'AccelCanonical' -- the default -- requires @Nat@, and for
-- the comparisons @Bool@, to be exactly the inductive types "Kernel.Canon" says
-- they are: same arity, same constructors in the same order, same types.  That
-- is not needed for soundness, which the equations already carry.  It is a
-- statement about what the kernel is willing to be surprised by: an environment
-- in which @Nat@ has a third constructor is one where the fast path and the
-- slow path agree on every numeral and nobody has thought about anything else,
-- and the cheap thing to do is decline.  'AccelVerified' keeps the equations
-- and drops that requirement, for a file that is deliberately unusual.

-- | An operation the kernel offers to compute directly on bignums.
data NatOp
  = Nat1 (Integer -> Integer)             -- ^ @Nat -> Nat@
  | Nat2 (Integer -> Integer -> Maybe Integer)
    -- ^ @Nat -> Nat -> Nat@; @Nothing@ declines this particular instance
  | Cmp2 (Integer -> Integer -> Bool)     -- ^ @Nat -> Nat -> Bool@

-- | The operations the kernel knows how to compute, and what it computes.
--
-- Being listed here is an /offer/, not a licence: 'natOpOk' decides whether the
-- offer is taken up, against the stored specification in "Kernel.Canon".  Every
-- name here must have an entry there, or it can never fire outside
-- 'AccelAlways'.
natOps :: [(Name, NatOp)]
natOps =
  [ (nameNatPred, Nat1 (\a -> max 0 (a - 1)))
  , (nameNatAdd,  Nat2 (\a b -> Just (a + b)))
  , (nameNatSub,  Nat2 (\a b -> Just (max 0 (a - b))))
  , (nameNatMul,  Nat2 (\a b -> Just (a * b)))
  , (nameNatPow,  Nat2 powBounded)
    -- Division by zero is total in this theory: @a / 0 = 0@ and @a % 0 = a@.
    -- Only reachable under 'AccelAlways'; see 'natOpCanon'.
  , (nameNatDiv,  Nat2 (\a b -> Just (if b == 0 then 0 else a `div` b)))
  , (nameNatMod,  Nat2 (\a b -> Just (if b == 0 then a else a `mod` b)))
  , (nameNatBEq,  Cmp2 (==))
  , (nameNatBLe,  Cmp2 (<=))
  , (nameNatBLt,  Cmp2 (<))
  ]

-- | 'natOps', indexed by 'nameHash'.
--
-- Every constant-headed term reduction looks at asks this question, and the
-- great majority of them are not arithmetic at all: the answer has to cost one
-- integer lookup rather than a walk down a list comparing names.
natOpTable :: IntMap [(Name, NatOp)]
natOpTable = IM.fromListWith (++) [ (nameHash n, [(n, op)]) | (n, op) <- natOps ]

lookupNatOp :: Name -> Maybe NatOp
lookupNatOp n = IM.lookup (nameHash n) natOpTable >>= lookup n

-- | @a ^ b@, unless the answer would not fit anywhere useful.
--
-- Declining is not a correctness matter -- the slow path cannot finish such a
-- case either -- but it decides /how/ the kernel fails on it: by running out of
-- time, which a caller can bound, rather than out of memory, which it cannot.
powBounded :: Integer -> Integer -> Maybe Integer
powBounded a b
  | a <= 1 || b <= 1                 = Just (a ^ b)
  | b > limit                        = Nothing
  | b * toInteger (bitLen a) > limit = Nothing
  | otherwise                        = Just (a ^ b)
  where
    limit = 1000000
    bitLen = go (0 :: Integer)
      where go acc 0 = acc
            go acc v = go (acc + 1) (v `div` 2)

-- | @f ⌜a⌝ ⌜b⌝ --> ⌜f a b⌝@, once 'natOpOk' says this @f@ computes that.
reduceNatOp :: Name -> NatOp -> [Expr] -> TC (Maybe Expr)
reduceNatOp n op args = natOpOk n >>= \ok -> if not ok then pure Nothing else
  case (op, args) of
    (Nat1 f, a : rest) -> natShape a >>= \sa -> pure $ case sa of
      NSLit x -> Just (mkApps (NatLit (f x)) rest)
      _       -> Nothing
    (Nat2 f, a : b : rest) -> do
      sa <- natShape a
      sb <- natShape b
      pure $ case (sa, sb) of
        (NSLit x, NSLit y) -> (\v -> mkApps (NatLit v) rest) <$> f x y
        _                  -> Nothing
    (Cmp2 f, a : b : rest) -> do
      sa <- natShape a
      sb <- natShape b
      pure $ case (sa, sb) of
        (NSLit x, NSLit y) -> Just (mkApps (boolOf (f x y)) rest)
        _                  -> Nothing
    _ -> pure Nothing
  where
    boolOf b = Const (if b then nameBoolTrue else nameBoolFalse) []

-- | How a @Nat@-valued term looks once reduced, as far as the equations care.
data NatShape
  = NSLit !Integer   -- ^ a numeral: a literal, or a @Nat.succ@ tower over one
  | NSSucc Expr      -- ^ @Nat.succ e@, with @e@ not read as a numeral
  | NSNeutral        -- ^ neither, and no further reduction will make it either

-- | Read a term as a numeral -- a literal, or @Nat.succ@ applied to one, or a
-- chain of those bottoming out at @Nat.zero@ -- and failing that, as a
-- successor of something, and failing that, as neither.
--
-- Reached only with 'natShapeOk' already established, since 'reduceNatOp' asks
-- 'natOpOk' first; that is what makes @Nat.succ ⌜k⌝@ and @⌜k+1⌝@ the same term
-- as far as conversion is concerned, and so lets the chain be folded away.
--
-- Folding is not a refinement.  @Nat.decLt n m@ is @Nat.decLe (Nat.succ n) m@,
-- so a comparison against a bound reaches the shortcut with one constructor
-- already peeled off; reading only bare literals would miss every @decide@ in
-- the prelude and leave the numeral to be counted down by hand.
--
-- The walk is bounded because the term it walks need not be finite in any useful
-- sense: 'natSymStep' turns @x + ⌜k⌝@ into @Nat.succ (x + ⌜k-1⌝)@, so a numeral
-- offset from an open term is a successor tower as deep as the numeral is large,
-- and reading it as a numeral is exactly what cannot be afforded.  Giving up
-- returns @NSSucc@, which is what the term is; only the arithmetic shortcut is
-- lost, and it was never going to fire on an open term anyway.
natShape :: Expr -> TC NatShape
natShape = go succWalk
  where
    go :: Int -> Expr -> TC NatShape
    go !d e = whnf e >>= \e' -> case e' of
      NatLit v | v >= 0 -> pure (NSLit v)
      _ -> case unApps e' of
        (Const c [], [])  | c == nameNatZero -> pure (NSLit 0)
        (Const c [], [a]) | c == nameNatSucc, d <= 0 -> pure (NSSucc a)
                          | c == nameNatSucc -> go (d - 1) a >>= \case
                              NSLit v -> pure (NSLit (v + 1))
                              _       -> pure (NSSucc a)
        _ -> pure NSNeutral

-- | How deep a @Nat.succ@ tower may be before 'natShape' stops reading it as a
-- numeral.  Anything a file writes by hand is one or two deep.
succWalk :: Int
succWalk = 256

-- | The arithmetic operations that recurse structurally on their second
-- argument.  All four are exported that way, and 'Kernel.Canon.natOpCanon'
-- states their equations in that shape.
natSymOps :: [Name]
natSymOps = [nameNatAdd, nameNatSub, nameNatMul, nameNatPow]

-- | 'natSymOps' membership, by hash; see 'natOpTable'.
natSymTable :: IntMap [Name]
natSymTable = IM.fromListWith (++) [ (nameHash n, [n]) | n <- natSymOps ]

isNatSymOp :: Name -> Bool
isNatSymOp n = maybe False (elem n) (IM.lookup (nameHash n) natSymTable)

-- | How large a numeral may be in the argument one of 'natSymOps' recurses on
-- before the kernel declines to unfold the operation at all.
--
-- The four are exported as structural recursions on that argument, so unfolding
-- one of them counts the numeral down: @x + ⌜k⌝@ with an open @x@ sets a
-- @brecOn@ going that builds @k@ levels of @Nat.below@ before it can say
-- anything.  For the numerals a file writes by hand that is a handful of steps.
-- For the ones a file /derives/ it is not: a signed bit width turns into an
-- offset of @2^31@ or @2^63@, and the two operands of the comparison it came
-- from are open terms, so the recursion runs to the end of the numeral and the
-- answer it eventually reaches is that there is no answer -- @x + ⌜k⌝@ has no
-- head constructor to find.  Two billion steps to learn that a term is stuck.
--
-- So past this bound the application is held whole.  Nothing is lost that could
-- have been gained: what the unfolding would have produced is the same term with
-- @k@ layers of arithmetic around it, and no conversion the kernel is asked
-- about is settled by walking them.  What is gained is that two such terms are
-- compared argument by argument, which is what they were always going to have to
-- be compared by.
--
-- Declining to unfold can only cost conversions, never grant them, so the bound
-- is a statement about effort and not about the theory.
heldNumeral :: Integer
heldNumeral = 4096

-- | Should this application be left alone rather than unfolded?  See
-- 'heldNumeral'.
--
-- Only a licensed operation is held: without a licence the kernel has no reason
-- to believe the name recurses the way the equations say, and unfolds it like
-- anything else.
natBlocked :: Name -> [Expr] -> TC Bool
natBlocked n args
  | isNatSymOp n, (_ : b : _) <- args =
      natOpOk n >>= \ok -> if not ok then pure False else held <$> natShape b
  | otherwise = pure False
  where
    held (NSLit k) = k > heldNumeral
    held _         = False

-- | May this operation be computed on bignums?
--
-- 'AccelOff' and 'AccelAlways' answer without looking at anything -- the second
-- is the whole soundness bug, reproduced on request.  The other two put the
-- declaration up against the stored specification in "Kernel.Canon".
--
-- Verified on a full budget and remembered for the environment: the answer is a
-- property of the environment, not of whatever the asking caller had left.  The
-- entry is parked at @False@ for the duration, so the conversion checks below
-- reduce the operation the ordinary way and cannot appeal to the shortcut they
-- are establishing.
natOpOk :: Name -> TC Bool
natOpOk n = do
  mode <- envAccel <$> getEnv
  case mode of
    AccelOff    -> pure False
    AccelAlways -> pure True
    _           -> cachedName tcNatOps n
                     (attempt (unmeteredly (verify mode)))
  where
    verify mode = case natOpCanon n of
      Nothing -> pure False
      Just c
        -- An operation with neither equations nor probes has no licence to be
        -- derived; only 'AccelAlways' reaches it, and that never gets here.
        | null (nocLaws c dummy dummy), null (nocProbes c) -> pure False
        | otherwise -> do
            shape <- natShapeOk
            inds  <- if mode == AccelCanonical
                       then and <$> mapM canonIndMatches (nocInds c)
                       else pure True
            ty    <- declaredTypeIs n (nocType c)
            deps  <- and <$> mapM natOpOk (nocDeps c)
            if not (shape && inds && ty && deps) then pure False else do
              laws <- withLocal (Binder (str "x")) nat $ \x ->
                      withLocal (Binder (str "y")) nat $ \y ->
                        allM (uncurry isDefEq) (nocLaws c (FVar x) (FVar y))
              if not laws then pure False else
                onBudget probeBudget (allM (uncurry isDefEq) (nocProbes c))
    nat   = Const nameNat []
    dummy = Const nameNatZero []

-- | Is this constant declared, with no universe parameters, at this type?
declaredTypeIs :: Name -> Expr -> TC Bool
declaredTypeIs n ty = do
  env <- getEnv
  case lookupConst env n of
    Just ci | null (constLevels ci) -> isDefEq (constType ci) ty
    _                               -> pure False

-- | Is the inductive type of this name the one "Kernel.Canon" describes?
--
-- Arity, constructor names, constructor order and every type, the last up to
-- conversion.  Constructor names /are/ checked here, unlike in the @Eq@ shape
-- test that guards @Quot.lift@: there the name carries no weight, whereas the
-- literal expansion and the arithmetic shortcuts both emit @Nat.zero@ and
-- @Nat.succ@ by name, so the names are part of what is being relied on.
--
-- Universe parameters are compared by position, under the file's own names, so
-- a type that differs only in what it calls its parameter still matches.
canonIndMatches :: CanonInd -> TC Bool
canonIndMatches c =
  cachedName tcCanonOk (ciName c)
             (attempt (unmeteredly go))
  where
    go = do
      env <- getEnv
      case lookupConst env (ciName c) of
        Just (CInd ind)
          | length (indLevels ind) == ciNumLevels c
          , indNumParams ind  == ciNumParams c
          , indNumIndices ind == ciNumIdx c
          , length (indCtors ind) == length (ciCtors c)
          , and (zipWith (\cn cc -> cn == ccName cc) (indCtors ind) (ciCtors c))
          -> do
            let us = indLevels ind
            okTy <- isDefEq (indType ind) (ciType c us)
            oks  <- mapM (ctorMatches env us) (zip (indCtors ind) (ciCtors c))
            pure (okTy && and oks)
        _ -> pure False

    ctorMatches env us (cn, cc) = case lookupConst env cn of
      Just (CCtor ci)
        | ctorInduct ci    == ciName c
        , ctorLevels ci    == us
        , ctorNumParams ci == ciNumParams c
        , ctorNumFields ci == ccNumFields cc
        -> isDefEq (ctorType ci) (ccType cc us)
      _ -> pure False

-- | Run a check, reading a failure as a "no".
--
-- The equations above mention constants that need not exist, so inferring a type
-- while checking them can fail outright.  For a question of the form "may this
-- shortcut be taken?" that is an answer.
--
-- What the abandoned check did to the state stands: 'TCState' is mutable and
-- there is no undo.  Nothing it can have done matters.  Every table it wrote to
-- is a cache; the locals it made are numbered from a counter that never reuses
-- an identifier, so they are dead rather than wrong; and the two things that are
-- neither -- the budget and the scope -- are put back by the combinators that
-- set them, on this path as on any other.
attempt :: TC Bool -> TC Bool
attempt (TC act) = TC $ \s -> act s >>= \case
  Left _ -> pure (Right False)
  ok     -> pure ok

-- | Is @cn@ a constructor of the inductive type @tn@, with no universe
-- parameters of its own beyond that type's, this many parameters and this many
-- fields?
isCtorOf :: Env -> Name -> (Name, Int, Int) -> Bool
isCtorOf env tn (cn, nps, nf) = case (lookupConst env tn, lookupConst env cn) of
  (Just (CInd ind), Just (CCtor ci)) ->
    ctorInduct ci == tn
      && ctorLevels ci == indLevels ind
      && ctorNumParams ci == nps
      && ctorNumFields ci == nf
      && indNumParams ind == nps
      && indNumIndices ind == 0
  _ -> False

-- | Does this closed term check against this type?  A failure is an answer, not
-- an error: the caller is asking whether an assumption holds, not relying on it.
wellTyped :: Expr -> Expr -> TC Bool
wellTyped e t = TC $ \s -> do
  r <- unTC (checkType e t) s
  pure (Right (either (const False) (const True) r))

-- | Run a check once per environment and remember the answer.
--
-- The slot is set to @False@ for the duration, so a check that somehow reached
-- 'expandLit' again would find literals inert and terminate rather than loop.
-- (Nothing currently does: the witnesses reduce only literal-free types.)
cached :: (TCState -> IORef (Maybe Bool)) -> TC Bool -> TC Bool
cached slot act = TC (\s -> Right <$> readIORef (slot s)) >>= \case
  Just b  -> pure b
  Nothing -> do
    note False
    b <- act
    note b
    pure b
  where note b = TC $ \s -> Right <$> writeIORef (slot s) (Just b)

-- | 'cached', for a question asked about one name out of many.  Parking at
-- @False@ matters more here: the checks these guard reduce the very operations
-- they are establishing, and would otherwise ask themselves.
cachedName :: (TCState -> IORef (Map Name Bool)) -> Name -> TC Bool -> TC Bool
cachedName slot n act = TC (\s -> Right . M.lookup n <$> readIORef (slot s)) >>= \case
  Just b  -> pure b
  Nothing -> do
    note False
    b <- act
    note b
    pure b
  where note b = TC $ \s -> Right <$> modifyIORef' (slot s) (M.insert n b)

-- | Decode a UTF-8 byte string into code points.
utf8Chars :: B.ByteString -> [Integer]
utf8Chars = go . map fromEnum . B.unpack
  where
    go [] = []
    go (c : cs)
      | c < 0x80  = toInteger c : go cs
      | c < 0xE0  = cont 1 (c - 0xC0) cs
      | c < 0xF0  = cont 2 (c - 0xE0) cs
      | otherwise = cont 3 (c - 0xF0) cs
    cont k acc cs =
      let (bs, rest) = splitAt k cs
          v = foldl (\a b -> a * 64 + (b - 0x80)) acc bs
      in toInteger v : go rest

-- Definitional equality -------------------------------------------------------

-- | Conversion.
--
-- A @True@ is worth remembering however it was arrived at.  A @False@ is worth
-- remembering only when the comparison that produced it was allowed to run to
-- the end, which is what 'unmeteredNow' asks: inside a 'speculate', @False@
-- means "not this way", and writing that down would answer a later caller's
-- honest question with a dead end.
--
-- A nested speculation that declines does /not/ spoil an unmetered answer.
-- 'sameHeadCongr' is the only rule that speculates, its refusal sends
-- 'defEqLoop' round to unfold both sides, and unfolding preserves conversion --
-- so the answer the unmetered call finally reaches is the one it would have
-- reached with congruence, only later.  This is the whole difference between
-- this guard and 'whnf''s: there, a starved reduction leaves a half-reduced
-- /term/ behind, and remembering that really would cost a later caller the
-- answer it was entitled to.
isDefEq :: Expr -> Expr -> TC Bool
isDefEq t0 s0
  | t0 == s0            = pure True
  | not (eqWorthMemo t0 s0) = decide
  | otherwise = lookupEq t0 s0 >>= \case
      Just b  -> pure b
      Nothing -> do
        full <- unmeteredNow
        b    <- decide
        when (b || full) (insertEq t0 s0 b)
        pure b
  where
    -- Not charged against the budget.  Charging a step per comparison is
    -- tempting -- congruence descends into arguments without reducing anything,
    -- so the budget does not bound the descent -- and it is a bad trade: it is
    -- deep spines of equal heads that congruence exists for, and a speculation
    -- that runs out part-way down one sends 'defEqLoop' off to unfold both
    -- heads instead, which is the expensive thing the rule was avoiding.  On
    -- Mathlib's category theory that turns a four-minute file into one that
    -- does not finish.  What the descent costs is bounded by the terms in front
    -- of it; what reduction costs is not, which is why reduction is what the
    -- budget counts.
    decide = outOfFuel >>= \out -> if out then pure False else do
      t <- whnfCore t0
      s <- whnfCore s0
      if t == s then pure True else defEqLoop t s

lookupEq :: Expr -> Expr -> TC (Maybe Bool)
lookupEq a b = TC $ \s -> do
  v <- eqGet s (eqMemo s a b) a b
  pure (Right v)

insertEq :: Expr -> Expr -> Bool -> TC ()
insertEq a b v = TC $ \s -> do
  eqInsert (eqMemo s a b) a b v
  pure (Right ())

defEqLoop :: Expr -> Expr -> TC Bool
defEqLoop t s = do
  m <- firstJustM [ tryBinders t s, tryEta t s, tryEta s t, trySortLit t s ]
  case m of
    Just b  -> pure b
    Nothing -> do
      cong <- tryRigidSpine t s
      case cong of
        Just True -> pure True
        _ -> do
          irrel <- tryProofIrrel t s
          if irrel then pure True else
            tryDelta t s >>= \case
              DEq       -> pure True
              DGo t' s' -> do
                t2 <- whnfCore t'
                s2 <- whnfCore s'
                if t2 == s2 then pure True else defEqLoop t2 s2
              -- Both heads are rigid, so 'tryRigidSpine' has already had its go.
              DStuck    -> lastResort t s
              DStarved  -> pure False

firstJustM :: [TC (Maybe a)] -> TC (Maybe a)
firstJustM []       = pure Nothing
firstJustM (a : as) = a >>= \case
  Just x  -> pure (Just x)
  Nothing -> firstJustM as

-- | Congruence for the two binders.  Definitive: if the domains or bodies
-- differ the terms are not convertible (nothing else can apply to a @Pi@ or a
-- @Lam@ in whnf).
tryBinders :: Expr -> Expr -> TC (Maybe Bool)
tryBinders (Lam n t1 b1) (Lam _ t2 b2) = Just <$> binderEq n t1 b1 t2 b2
tryBinders (Pi  n t1 b1) (Pi  _ t2 b2) = Just <$> binderEq n t1 b1 t2 b2
tryBinders _ _                         = pure Nothing

binderEq :: Binder -> Expr -> Expr -> Expr -> Expr -> TC Bool
binderEq n t1 b1 t2 b2 = do
  okT <- isDefEq t1 t2
  if not okT then pure False else
    withLocal n t1 $ \x -> isDefEq (instantiateBody x b1) (instantiateBody x b2)

-- | Function eta: @f = fun x => f x@.
tryEta :: Expr -> Expr -> TC (Maybe Bool)
tryEta (Lam n dom body) s = do
  let s' = Lam n dom (App (liftE 0 1 s) (BVar 0))
  Just <$> isDefEq (Lam n dom body) s'
tryEta _ _ = pure Nothing

-- | @Sort@s, literals, and literal-versus-constructor.
trySortLit :: Expr -> Expr -> TC (Maybe Bool)
trySortLit (Sort a)   (Sort b)   = pure (Just (levelEquiv a b))
trySortLit (NatLit a) (NatLit b) = pure (Just (a == b))
trySortLit (StrLit a) (StrLit b) = pure (Just (a == b))
trySortLit a b
  | isLit a, headIsCtorish b = do a' <- expandLit a; Just <$> isDefEq a' b
  | isLit b, headIsCtorish a = do b' <- expandLit b; Just <$> isDefEq a b'
  where
    isLit NatLit{} = True
    isLit StrLit{} = True
    isLit _        = False
    headIsCtorish e = case headOf e of Const{} -> True; _ -> False
trySortLit _ _ = pure Nothing

-- | Where a constant's result type lives.
--
-- @Just (n, ps, u)@ says the declared type is a telescope of @n@ binders, and
-- that the body of that telescope -- the type of @c a1 .. an@ -- is a @Sort u@,
-- with @u@ written in terms of the level parameters @ps@ the constant was
-- declared over.  A use site substitutes its own level arguments into it.
--
-- Read off declared types only, without reducing anything, so @Nothing@ means
-- /do not know/ rather than /no/.  Cached by name, because 'notAProof' asks
-- about the same handful of heads millions of times.
resultUniverse :: Name -> TC (Maybe ([Name], Level))
resultUniverse n = do
  known <- TC $ \s -> Right . M.lookup n <$> readIORef (tcSortRes s)
  case known of
    Just r  -> pure r
    Nothing -> do
      genv <- getEnv
      let r = do ci       <- lookupConst genv n
                 (ctx, b) <- Just (splitPis [] (constType ci))
                 u        <- univOf genv univDepth ctx b
                 pure (constLevels ci, u)
      TC $ \s -> Right <$> modifyIORef' (tcSortRes s) (M.insert n r)
      pure r
  where
    splitPis ctx (Pi _ t b) = splitPis (t : ctx) b
    splitPis ctx b          = (ctx, b)

-- | How far 'univOf' will chase a head through other declarations' types.
--
-- A bound rather than a cycle check: the environment is built in dependency
-- order, so a declaration's type cannot mention the declaration itself, and
-- this only exists so that no amount of nesting can make the question
-- expensive.
univDepth :: Int
univDepth = 8

-- | @Just u@ when @e@ is a type living in universe @u@ -- when @e : Sort u@ --
-- as far as the declared type of its head says, without reducing anything.
--
-- @ctx@ holds the types of the enclosing binders, innermost first, so that a
-- 'BVar' head can be looked up.
univOf :: Env -> Int -> [Expr] -> Expr -> Maybe Level
univOf env d ctx e
  | d <= 0    = Nothing
  | otherwise = case e of
      Sort u   -> Just (mkSucc u)
      -- @(x : t) -> b : Sort (imax _ u)@, which is zero exactly when @u@ is.
      Pi _ t b -> univOf env (d - 1) (t : ctx) b
      _        -> case headOf e of
        Const c ls -> do
          ci     <- lookupConst env c
          (_, u) <- teleSort env (d - 1) 0 (constType ci)
          Just (instLevelParams (constLevels ci) ls u)
        BVar i -> do
          t      <- nth i ctx
          (_, u) <- teleSort env (d - 1) 0 t
          Just u
        _ -> Nothing
  where
    nth _ []       = Nothing
    nth 0 (x : _)  = Just x
    nth k (_ : xs) = nth (k - 1 :: Int) xs

-- | A telescope ending in a sort: how many binders, and which sort.
--
-- A definition standing between the two is unfolded, because the class
-- hierarchy is full of binders declared @outParam (Type u)@ and an argument
-- whose type is a type is exactly what has to be recognised here.
teleSort :: Env -> Int -> Int -> Expr -> Maybe (Int, Level)
teleSort env d !k e = case e of
  Pi _ _ b -> teleSort env d (k + 1) b
  Sort u   -> Just (k, u)
  _ | d <= 0    -> Nothing
    | otherwise -> case unApps e of
        (Const c ls, as) -> do
          ci <- lookupConst env c
          v  <- case ci of CDef di -> Just (defValue di); _ -> Nothing
          teleSort env (d - 1) k
                   (betaApply (instLevelsE (constLevels ci) ls v) as)
        _ -> Nothing

-- | A term that is patently not a proof, decided without inferring its type.
--
-- \"Not a proof\" means the type of its type is not @Prop@.  A sort, a pi and a
-- literal are ruled out on sight.  Beyond those, the question is settled by the
-- declared type of the term's head: if @c@ is declared @forall x1 .. xn, T@ and
-- 'univOf' can say that @T@ lives in a universe that is definitely not zero,
-- then @c a1 .. ak : forall rest, T@ for @k <= n@ lives in @Sort (imax .. u)@,
-- and an @imax@ whose right argument is nonzero is nonzero, so the term's type
-- is not a proposition.
--
-- 'univOf' is what makes this worth having.  Reading @T@ for a syntactic @Sort@
-- catches @Nat.le@ and @Eq@ but nothing that computes: the terms that actually
-- turn up here are stuck arithmetic and stuck eliminators -- @Nat.mul a b@,
-- @Int.casesOn motive i _ _@, @HAdd.hAdd _ _ _ inst a b@ -- whose declared
-- result is an inductive type, a bound type variable, or a motive applied to
-- its major premise.  Each of those has a universe that can still be read off
-- without reduction, one indirection further in.
--
-- The point is that 'tryProofIrrel' is asked millions of times per hard
-- declaration and answers @False@ essentially every time, because what it is
-- being asked about is usually two /values/ being compared rather than two
-- proofs -- and finding that out its own way costs two inferences and the
-- reductions they set off.  A @True@ here has to be right; a @False@ only costs
-- the slow route.
notAProof :: Expr -> TC Bool
notAProof e = case e of
  Sort{}   -> pure True
  Pi{}     -> pure True
  NatLit{} -> pure True
  StrLit{} -> pure True
  _        -> case headOf e of
    Const c ls -> resultUniverse c >>= \case
      Just (ps, u) -> pure (isDefinitelyNonZero
                              (if null ps then u else instLevelParams ps ls u))
      Nothing      -> pure False
    _ -> pure False

-- | Proof irrelevance: any two proofs of the same proposition are equal.
tryProofIrrel :: Expr -> Expr -> TC Bool
tryProofIrrel t s = notAProof t >>= \no -> if no then pure False else
                    outOfFuel >>= \out -> if out then pure False else do
  tt <- inferOnly t
  l  <- ensureSort =<< inferOnly tt
  if not (isDefinitelyZero l) then pure False else do
    ts <- inferOnly s
    isDefEq tt ts

-- | Congruence for a spine whose head cannot be unfolded -- a local constant, a
-- projection, an axiom, a constructor, an inductive type, a stuck recursor.
--
-- Tried early, and only for such heads.  It is not speculative (there is
-- nothing else the pair could reduce to), it costs nothing when the heads
-- differ, and getting it in before 'tryProofIrrel' is what keeps the kernel
-- from inferring the type of every intermediate term of a long computation.
-- For a head that /is/ a definition the same congruence is speculative -- the
-- two sides may only agree after unfolding -- so it is left to 'tryDelta',
-- which weighs it against the definition heights.
tryRigidSpine :: Expr -> Expr -> TC (Maybe Bool)
tryRigidSpine t s = do
  unfoldable <- isUnfoldableHead t
  if unfoldable then pure Nothing else trySpine t s

-- | May delta take a step on this application, and at what priority?
--
-- \"May\" has to mean exactly what 'unfoldDelta' will do, which is why this
-- looks at the arguments and not only at the head: an arithmetic application
-- over a large numeral is /held/ (see 'natBlocked'), and a caller told that its
-- head is a definition would keep being promised a reduction that never
-- arrives.  A held application is therefore reported the same way a local
-- constant or an axiom is -- as rigid -- which is also the right thing for
-- 'tryRigidSpine', since congruence is the only rule left for it.
deltaHead :: Expr -> TC (Maybe Hint)
deltaHead e = case headOf e of
  Const n ls -> lookupConstC n >>= \case
      Just (CDef d) | length ls == length (defLevels d) -> do
        -- The arguments are only wanted for the four operations that can be
        -- held, and taking a spine apart is not free, so the cheap half of
        -- 'natBlocked''s guard is repeated here rather than paid for everywhere.
        held <- if isNatSymOp n
                  then natBlocked n (argsOf e)
                  else pure False
        pure (if held then Nothing else Just (defPriority d))
      _ -> pure Nothing
  _ -> pure Nothing

-- | Is the head of this application a definition the kernel may delta-unfold?
isUnfoldableHead :: Expr -> TC Bool
isUnfoldableHead e = maybe False (const True) <$> deltaHead e

-- | The outcome of one round of lazy delta unfolding.
--
-- @DStarved@ is not a statement about the terms: it says the budget ran out
-- before anything could be unfolded, so this round made no progress and the
-- loop must stop rather than ask the same question again.
data Delta = DEq | DGo Expr Expr | DStuck | DStarved

-- | Lazy delta reduction: unfold the taller definition first, and when both
-- sides are the same constant try congruence before unfolding at all.
--
-- \"Taller\" is read off 'defPriority', which ranks a proof below every ordinary
-- definition however tall it is.  Nothing about which terms are convertible
-- depends on the order -- when neither side wins, both are unfolded -- but a
-- great deal about how long finding out takes.
--
-- The preferred side may decline: 'deltaHead' and 'unfoldDelta' agree on which
-- applications are held, but not on whether the budget will still be there when
-- the unfolding is asked for.  So a refusal falls through to the other side, and
-- only a round in which neither side moved ends the loop.
tryDelta :: Expr -> Expr -> TC Delta
tryDelta t s = outOfFuel >>= \out -> if out then pure DStarved else do
  ht <- deltaHead t
  hs <- deltaHead s
  case (ht, hs) of
    (Nothing, Nothing) -> pure DStuck
    (Just _,  Nothing) -> leftFirst
    (Nothing, Just _)  -> rightFirst
    (Just a,  Just b)
      | a > b     -> leftFirst
      | b > a     -> rightFirst
      | otherwise -> do
          same <- sameHeadCongr t s
          if same then pure DEq else bothSides
  where
    -- Every exit reports what actually happened.  Answering @DGo t s@ with the
    -- terms it was handed would ask the caller to compare them again, which is
    -- what it just did: 'defEqLoop' would spin.  So a round that unfolds
    -- nothing is a round that ends, and the two reasons for unfolding nothing
    -- are told apart -- 'DStarved' means the loop stops because the budget did,
    -- 'DStuck' means there is nothing left to try.
    leftFirst = unfoldDelta t >>= \case
      Just t' -> pure (DGo t' s)
      Nothing -> rightOnly
    rightFirst = unfoldDelta s >>= \case
      Just s' -> pure (DGo t s')
      Nothing -> leftOnly
    leftOnly = unfoldDelta t >>= \case
      Just t' -> pure (DGo t' s)
      Nothing -> nothingDoing
    rightOnly = unfoldDelta s >>= \case
      Just s' -> pure (DGo t s')
      Nothing -> nothingDoing
    bothSides = do
      mt <- unfoldDelta t
      ms <- unfoldDelta s
      case (mt, ms) of
        (Nothing, Nothing) -> nothingDoing
        _ -> pure (DGo (maybe t id mt) (maybe s id ms))
    nothingDoing = outOfFuel >>= \out -> pure (if out then DStarved else DStuck)

-- | If both sides are the same constant applied to the same number of
-- arguments, try comparing arguments pairwise.  A failure here is /not/
-- conclusive -- the terms may still be equal after unfolding -- so the caller
-- falls through rather than reporting inequality.
--
-- Which is also why it runs on a budget.  The arguments the two sides disagree
-- on may be exactly the ones unfolding the head is about to throw away, and
-- normalising them can cost arbitrarily more than the comparison the caller
-- actually wants.  See 'speculate'.
sameHeadCongr :: Expr -> Expr -> TC Bool
sameHeadCongr t s = case (unApps t, unApps s) of
  ((Const n1 l1, as1), (Const n2 l2, as2))
    | n1 == n2, length l1 == length l2, length as1 == length as2
    , and (zipWith levelEquiv l1 l2) ->
        speculate (allM (uncurry isDefEq) (zip as1 as2))
  _ -> pure False

-- | Everything that only makes sense once no more unfolding is possible.
lastResort :: Expr -> Expr -> TC Bool
lastResort t s = do
  m <- firstJustM
    [ tryProjCongr t s
    , tryNatOffset t s
    , tryStructEta t s
    , tryStructEta s t
    , tryUnitLike t s
    ]
  pure (maybe False id m)

-- | Congruence for a neutral spine (local constant, axiom, constructor,
-- inductive type, stuck recursor, stuck projection, ...).
--
-- Sound but incomplete, so a failure only means \"try something else\".
trySpine :: Expr -> Expr -> TC (Maybe Bool)
trySpine t s = case (unApps t, unApps s) of
  ((h1, as1), (h2, as2))
    | length as1 == length as2 -> do
        heads <- headEq (null as1) h1 h2
        if heads then yesOrPass =<< allM (uncurry isDefEq) (zip as1 as2)
                 else pure Nothing
  _ -> pure Nothing
  where
    yesOrPass b = pure (if b then Just True else Nothing)
    headEq _ (FVar i) (FVar j) = pure (i == j)
    headEq _ (Const n1 l1) (Const n2 l2) =
      pure (n1 == n2 && length l1 == length l2 && and (zipWith levelEquiv l1 l2))
    -- A stuck projection can head an application too -- @(x.1) y@ -- and then
    -- the two projected structures may still need unfolding to be compared.
    -- Only recurse when there really are arguments: with none, this /is/ the
    -- call 'tryProjCongr' is about to make, and we would loop.
    headEq False p@Proj{} q@Proj{} = isDefEq p q
    headEq _ _ _ = pure False

tryProjCongr :: Expr -> Expr -> TC (Maybe Bool)
tryProjCongr (Proj n1 i1 s1) (Proj n2 i2 s2)
  | n1 == n2, i1 == i2 = do
      b <- isDefEq s1 s2
      pure (if b then Just True else Nothing)
tryProjCongr _ _ = pure Nothing

-- | Two numerals offset from the same term: @Nat.succ (x + ⌜k⌝)@ against
-- @x + ⌜k+1⌝@.
--
-- This is the conversion §6.5's held numeral takes away, and it is not the
-- exotic one that section expected to lose.  @Char@'s bounds proofs are full of
-- it: a lemma states @x + ⌜57344⌝ + ⌜1⌝ ≤ ⌜1114112⌝@ and is used where
-- @x + ⌜57345⌝ ≤ ⌜1114112⌝@ is wanted.  Reduction gets the first to
-- @Nat.succ (x + ⌜57344⌝)@ -- the outer @+1@ is small enough to unfold -- and
-- there it stops, because the second is over a numeral too large to unfold and
-- is held.  One side is a successor, the other is an addition, and no congruence
-- rule relates them.
--
-- So relate them by what they are: both sides are read as a base term and a
-- numeral offset, and two such are convertible when the offsets agree and the
-- bases do.  The two equations that makes this a derivation rather than a guess
-- -- @x + 0 ≡ x@ and @x + succ y ≡ succ (x + y)@ -- are the ones 'natOpOk' has
-- already checked against this file's own @Nat.add@, so the rule is only offered
-- where that licence holds; without it @Nat.add@ is not held in the first place
-- and reduction handles the pair on its own.
--
-- Only offered when one of the two /is/ held, which is the only way this pair
-- reaches a stuck comparison at all.  That keeps the reading off every other
-- last-resort comparison, and it is also what makes the rule cheap: it is
-- undoing a specific refusal, in the one place that refusal shows.
tryNatOffset :: Expr -> Expr -> TC (Maybe Bool)
tryNatOffset t s = do
  ht <- heldSide t
  hs <- if ht then pure True else heldSide s
  if not (ht || hs) then pure Nothing else natOpOk nameNatAdd >>= \ok ->
    if not ok then pure Nothing else do
      (bt, kt) <- natOffset t
      (bs, ks) <- natOffset s
      -- Offsets of zero are two terms with no arithmetic in them, which is
      -- every other rule's business and not this one's.
      if kt /= ks || kt == 0 then pure Nothing else do
        b <- isDefEq bt bs
        pure (if b then Just True else Nothing)
  where
    heldSide e = case unApps e of
      (Const n _, args) -> natBlocked n args
      _                 -> pure False

-- | Read a term as @base + k@ with @k@ a numeral, reducing as far as it takes to
-- see the shape.
--
-- Reducing is the point.  The terms this is asked about have had their heads
-- normalised and nothing else, so the first thing under a @Nat.succ@ is
-- typically an unreduced @HAdd.hAdd@ tower with the interesting numeral several
-- instance projections down.  Each layer is therefore 'whnf'\'d before it is
-- read, which stops of its own accord at the held application this rule exists
-- to look inside.
--
-- The walk is bounded for the same reason 'natShape'\'s is: nothing stops a term
-- from being a successor tower deeper than anyone wants to count, and giving up
-- costs only this rule on this pair.
natOffset :: Expr -> TC (Expr, Integer)
natOffset = go offsetWalk 0
  where
    go :: Int -> Integer -> Expr -> TC (Expr, Integer)
    go !d !acc e0 = do
      e <- whnf e0
      if d <= 0 then pure (e, acc) else case unApps e of
        (Const c [], [])     | c == nameNatZero -> pure (NatLit 0, acc)
        (Const c [], [a])    | c == nameNatSucc -> go (d - 1) (acc + 1) a
        (Const c [], [a, b]) | c == nameNatAdd  -> natShape b >>= \case
            NSLit k -> go (d - 1) (acc + k) a
            _       -> pure (e, acc)
        _ -> case e of
          NatLit v | v >= 0 -> pure (NatLit 0, acc + v)
          _                 -> pure (e, acc)

-- | How many @+ ⌜k⌝@ and @Nat.succ@ layers 'natOffset' will read through.
offsetWalk :: Int
offsetWalk = 256

-- | If one side is a constructor application of a structure, expand the other
-- side into one via projections.
tryStructEta :: Expr -> Expr -> TC (Maybe Bool)
tryStructEta t s = withFuel $ do
  env <- getEnv
  case unApps t of
    (Const cn _, as) -> lookupConstC cn >>= \case
      Just (CCtor ci)
        | isStructureLike env (ctorInduct ci)
        , length as == ctorNumParams ci + ctorNumFields ci
        , ctorNumFields ci > 0 -> do
            sTy <- inferOnly s >>= whnf
            case headOf sTy of
              Const tn _ | tn == ctorInduct ci -> do
                let fields = drop (ctorNumParams ci) as
                b <- allM (\(i, f) -> isDefEq f (Proj tn i s)) (zip [0 ..] fields)
                pure (if b then Just True else Nothing)
              _ -> pure Nothing
      _ -> pure Nothing
    _ -> pure Nothing

-- | A structure with no fields has exactly one element up to conversion.
tryUnitLike :: Expr -> Expr -> TC (Maybe Bool)
tryUnitLike t s = withFuel $ do
  env <- getEnv
  tTy <- inferOnly t >>= whnf
  case headOf tTy of
    Const tn _
      | isStructureLike env tn
      , Just ci <- ctorOfStructure env tn
      , ctorNumFields ci == 0 -> do
          sTy <- inferOnly s
          b <- isDefEq tTy sTy
          pure (if b then Just True else Nothing)
    _ -> pure Nothing

allM :: (a -> TC Bool) -> [a] -> TC Bool
allM _ []       = pure True
allM f (x : xs) = f x >>= \b -> if b then allM f xs else pure False

-- Inference -------------------------------------------------------------------

-- | How hard 'inferM' works.
--
-- @Verify@ is the real typing judgement: every premise of every rule is
-- checked.  @Assume@ computes the /same/ type but takes the premises on trust,
-- so it only walks the term's head spine and binders instead of the whole term.
--
-- @Assume@ is sound to use exactly when the term is already known to typecheck,
-- because then the premises it skips are known to hold.  That is a standing
-- invariant of 'whnf' and 'isDefEq': a term only reaches them after 'checkType'
-- has been through it (a subterm of a checked term is checked, and the types
-- 'ensurePi' / 'ensureSort' hand around are types of checked terms).  The
-- conversion checker leans on this heavily -- 'tryProofIrrel' asks for the type
-- of both sides of every stuck comparison, and re-verifying those terms turns a
-- linear check into a quadratic one.
data InferMode = Verify | Assume deriving Eq

-- | The local environment an /open/ term is read in: the local constants the
-- enclosing binders were opened with, innermost first, so that @BVar i@ denotes
-- @FVar (env !! i)@.
--
-- Inference carries one of these instead of substituting at every binder.  The
-- invariant is asymmetric, and worth stating precisely:
--
-- * @inferM m env e@ may be given an @e@ that is open with respect to @env@;
-- * the type it returns is always /closed/ -- every variable in it is an
--   'FVar' with an entry in the local context.
--
-- That is what makes the environment cheap: it is threaded down through
-- 'Lam' and 'Pi' without touching the body, and materialised (by 'closeIn')
-- only where a subterm has to be handed to something that needs a real term --
-- a binder type going into the local context, an argument being substituted
-- into a dependent codomain, the structure of a projection.
--
-- Substituting instead, as the rules are written in SPEC.md, is quadratic: a
-- telescope of @n@ binders copies its whole body @n@ times.
--
-- The locals are held as the 'FVar' nodes that stand for them rather than as
-- their identifiers, because that is the form 'closeIn' hands to 'instN': a
-- list of identifiers has to have a node built for each of them at every call,
-- and 'closeIn' is called at every argument, every binder type and every
-- projection the checker reads.
type LEnv = [Expr]

-- | Extend an environment with the local a binder introduces.  The only way one
-- is built, which is what lets 'envKey' read the identifier back out.
extendLEnv :: Int -> LEnv -> LEnv
extendLEnv x env = FVar x : env

-- | The environment half of a 'Memo' key, for a term with loose bound
-- variables.
--
-- Just the innermost local, which identifies the whole list: 'freshFVar' hands
-- out an id that has never been used before and inference immediately conses it
-- onto one particular environment, so no id is ever the head of two different
-- ones.  @-1@ is not an id, so it can stand for the empty environment -- which
-- is the only thing the second equation can be reading, by 'extendLEnv'.
envKey :: LEnv -> Int
envKey (FVar x : _) = x
envKey _            = -1

-- | The environment half of a 'Memo' key for @e@.
--
-- The answer depends on the environment only through the entries the term's
-- loose bound variables name, so a term that has none is read the same way
-- everywhere and every environment shares one entry -- the same one the empty
-- environment uses.  A term that has some names the innermost, so its whole
-- environment is pinned by 'envKey' and nothing is gained by looking further.
--
-- Sharing that entry is not a refinement, it is the difference between linear
-- and exponential.  A binder infers its body under a /fresh/ local, so keying on
-- the environment alone gives a subterm reached under @n@ binders @n@ distinct
-- keys -- and a subterm reached along @2^n@ paths, @2^n@ of them, each with its
-- own chain of fresh locals to allocate.  A closed term under a binder is the
-- common case (@∀ x : A, B@ with @B@ not mentioning @x@ is one), so this is not
-- a corner: it is what stops a deeply shared type from being unfolded into the
-- tree it denotes.
memoKey :: LEnv -> Expr -> Int
memoKey env e | looseBVarRange e == 0 = -1
              | otherwise             = envKey env

-- | Replace the loose bound variables of a term by what @vs@ says they stand
-- for, leaving a closed term.  A term needing more than @vs@ supplies is
-- out of scope, and is rejected here rather than silently renumbered.
substIn :: [Expr] -> Expr -> TC Expr
substIn vs e
  | k == 0    = pure e
  | supplies k vs = pure (instNPrefix k vs e)
  | otherwise = throwTC ("loose bound variable #" ++ show (k - 1))
  where
    k = looseBVarRange e
    supplies 0 _        = True
    supplies _ []       = False
    supplies j (_ : xs) = supplies (j - 1 :: Int) xs

-- | 'substIn' for the variables an environment binds, memoised.
--
-- The memo is the same shape as inference's, and keyed the same way, because it
-- is answering a question of the same two things: an open node and the
-- environment it is read in.  It is worth having for the same reason too.
-- 'inferM' materialises the argument of every application it reads -- @closeIn
-- env a@ -- and it is memoised on @(a, env)@, so a node the memo already has an
-- answer for is never inferred twice; but the /argument/ of that application was
-- closed on the way in, and closing it again is a full rebuild of the term.
-- Reduction hands the same spine back to inference over and over, so this was
-- the largest single source of allocation in the checker.
--
-- Nothing invalidates it.  Unlike inference and whnf, what it computes does not
-- consult the environment or the universe parameters at all: it is
-- @instNPrefix@ of a term against a list, and 'envKey' pins that list for the
-- lifetime of the state -- see 'freshFVar', whose supply only ever goes up.  So
-- it sits with 'tcLevelInst' among the tables 'forgetMemos' leaves alone.
--
-- Only 'closeIn' may be memoised, not 'substIn': 'inferCore' substitutes a
-- @let@ value into a body with @substIn (v' : env) b@, and @v'@ is not the
-- 'FVar' of a binder, so 'envKey' would read the environment underneath it and
-- name the wrong list.
closeIn :: LEnv -> Expr -> TC Expr
closeIn env e
  | looseBVarRange e == 0 = pure e
  | otherwise = lookupClose ek e >>= \case
      Just v  -> pure v
      Nothing -> do
        v <- substIn env e
        insertClose ek e v
        pure v
  where ek = envKey env

lookupClose :: Int -> Expr -> TC (Maybe Expr)
lookupClose ek e = TC $ \s -> Right <$> memoGet s (tcCloseIn s) ek e

insertClose :: Int -> Expr -> Expr -> TC ()
insertClose ek k v = TC $ \s -> do
  memoInsert (tcCloseIn s) ek k v
  pure (Right ())

infer :: Expr -> TC Expr
infer = inferM Verify []

-- | The type of a term that is already known to typecheck.  See 'InferMode'.
inferOnly :: Expr -> TC Expr
inferOnly = inferM Assume []

-- | The typing judgement, memoised on the node and its environment.
--
-- The memo is not an optimisation of a linear traversal: without it inference
-- runs over the term's /tree unfolding/, which for a shared term is
-- exponentially larger than the term.  Two nodes get the same type whenever
-- they are the same node read in the same environment, because with those and
-- the global environment and the declaration's universe parameters fixed the
-- judgement is a function of the term -- see 'Memo', 'memoKey' and 'swapEnv'.
inferM :: InferMode -> LEnv -> Expr -> TC Expr
inferM m env e
  | trivial e = inferCore m env e
  | otherwise = lookupInfer m ek e >>= \case
      Just t  -> pure t
      Nothing -> do
        t <- inferCore m env e
        insertInfer m ek e t
        pure t
  where
    ek = memoKey env e
    -- Leaves cost less to infer than to look up.
    trivial ex = case ex of
      App{} -> False; Lam{} -> False; Pi{} -> False
      Let{} -> False; Proj{} -> False; _ -> True

lookupInfer :: InferMode -> Int -> Expr -> TC (Maybe Expr)
lookupInfer m ek e = TC $ \s -> do
  v <- memoGet s (inferMemo m s e) ek e
  pure (Right v)

insertInfer :: InferMode -> Int -> Expr -> Expr -> TC ()
insertInfer m ek k v = TC $ \s -> do
  memoInsert (inferMemo m s k) ek k v
  pure (Right ())

inferCore :: InferMode -> LEnv -> Expr -> TC Expr
inferCore m env e = case e of
  BVar i      -> case drop i env of
    (FVar x : _) -> localType x
    _            -> throwTC ("loose bound variable #" ++ show i)
  FVar i      -> localType i
  Sort l      -> do when (m == Verify) (checkLevel l); pure (Sort (LSucc l))
  NatLit _    -> pure (Const nameNat [])
  StrLit _    -> pure (Const nameString [])
  Const n ls  -> lookupConstC n >>= \case
      Nothing -> throwTC ("unknown constant " ++ showName n)
      Just ci -> do
        let ps = constLevels ci
        unless (length ls == length ps) $
          throwTC ("constant " ++ showName n ++ " expects " ++ show (length ps)
                   ++ " universe arguments, got " ++ show (length ls))
        when (m == Verify) (mapM_ checkLevel ls)
        instLevels ps ls (constType ci)
  -- A whole spine at once, and not one application node at a time.  Taken a
  -- node at a time, the type of @h a1 ... an@ is built by substituting @a1@
  -- into the telescope of @h@'s type, then @a2@ into what is left of it, and so
  -- on: @n@ copies of a telescope @n@ binders long, to arrive at a type that
  -- mentions each argument once.  Here the binders are peeled off as the
  -- arguments are read and the arguments are held back in @vs@, so each
  -- /domain/ is instantiated -- those are one argument's type each, and small --
  -- and the body is instantiated once at the end.
  --
  -- Mathlib is where this shows: a typeclass-heavy statement is a spine of ten
  -- or fifteen arguments over a long telescope, and rebuilding that telescope
  -- for each of them was a third of everything the statement pass allocated.
  --
  -- What is given up is the memo entry for each proper prefix of the spine.
  -- @h a1@ is still inferred, and memoised, wherever it occurs as a term in its
  -- own right; it is no longer inferred as a step towards @h a1 a2@.
  App{} -> case unApps e of
    (h, as) -> inferM m env h >>= \th -> spine th as []
  Lam n t b -> do
    when (m == Verify) (() <$ inferSortOfIn env t)
    sharedLocal env n t $ \x t' -> do
      tb <- inferM m (extendLEnv x env) b
      pure (Pi n t' (abstractFVars [x] tb))
  Pi n t b -> do
    -- Both sorts are part of the /result/, not a premise, so they are computed
    -- in either mode; only the recursive verification of @t@ and @b@ is dropped.
    l1 <- ensureSort =<< inferM m env t
    sharedLocal env n t $ \x _ -> do
      l2 <- ensureSort =<< inferM m (extendLEnv x env) b
      pure (Sort (mkIMax l1 l2))
  Let _ t v b -> do
    t' <- closeIn env t
    when (m == Verify) $ do
      _ <- inferSortOf t'
      checkTypeIn env v t'
    v' <- closeIn env v
    -- Zeta: the body is read with the value in place of the let-bound variable.
    b' <- substIn (v' : env) b
    inferM m [] b'
  Proj tn i s -> inferProj m env tn i s
  where
    -- @spine ty as vs@ types a head already applied to some arguments, and now
    -- applied to @as@ as well.  @ty@ is what is left of the head's type after
    -- the binders those earlier arguments used were peeled off, so its loose
    -- variables stand for them, innermost first; @vs@ is what they stand for,
    -- in that order, waiting to be put in.
    --
    -- The invariant is @looseBVarRange ty <= length vs@: the head's type is
    -- closed, and peeling one binder off it can leave at most one more variable
    -- loose than the last, which is exactly what taking one more argument adds
    -- to @vs@.  So 'instN' below always has something for every variable it
    -- meets and nothing is left over to be lowered.
    spine ty [] vs = pure (instN vs ty)
    spine ty (a : as) vs = case ty of
      Pi _ dom cod -> next dom cod a as vs
      -- Not a binder yet.  Whatever it reduces to is closed -- the pending
      -- arguments went in on the way -- so the rest of the spine starts over
      -- with nothing pending.
      _ -> do (dom, cod) <- ensurePi (instN vs ty)
              next dom cod a as []

    next dom cod a as vs = do
      when (m == Verify) (checkTypeIn env a (instN vs dom))
      -- The argument is only needed as a term when what follows looks at it --
      -- and if nothing that follows looks at anything, the ones held back so
      -- far are not needed either.
      if looseBVarRange cod == 0
        then spine cod as []
        else do a' <- closeIn env a
                spine cod as (a' : vs)

-- | @checkType e t@ fails unless @e : t@.
checkType :: Expr -> Expr -> TC ()
checkType = checkTypeIn []

-- | @checkTypeIn env e t@ checks a term open with respect to @env@ against a
-- closed type.
checkTypeIn :: LEnv -> Expr -> Expr -> TC ()
checkTypeIn env e t = do
  te <- inferM Verify env e
  ok <- isDefEq te t
  unless ok $ do
    e'  <- closeIn env e
    te' <- whnf te
    t'  <- whnf t
    throwTC ("type mismatch:\n  term     " ++ brief e'
             ++ "\n  has type " ++ brief te'
             ++ "\n  expected " ++ brief t')

-- | Terms in error messages are for a human; a term the size of a proof term is
-- not.
brief :: Expr -> String
brief e = case splitAt 400 (showExpr e) of
  (s, [])  -> s
  (s, _)   -> s ++ " ..."

-- | Infer a type and require it to be a @Sort@, returning its level.
inferSortOf :: Expr -> TC Level
inferSortOf = inferSortOfIn []

inferSortOfIn :: LEnv -> Expr -> TC Level
inferSortOfIn env e = inferM Verify env e >>= ensureSort

-- | Which sort a type will turn out to live in, taken on trust.
--
-- This is 'inferSortOf' in @Assume@ mode, and the difference is not a shortcut
-- but a change of shape.  Every premise is skipped, and the largest of them is
-- the one at an application: the argument is never looked at, only the
-- function's telescope is walked.  So where the real judgement reads the whole
-- of a term, this reads one path through it -- the leftmost spine -- and a
-- statement of a hundred nodes costs about as much as a statement of ten.
--
-- Whenever 'inferSortOf' succeeds this agrees with it, because the two differ
-- only by checks whose result is @()@ (see 'InferMode').  On a type that is not
-- well formed the answer is a guess: it may be a level no reading of the type
-- justifies, or the walk may fail where the real judgement would not have got
-- that far.  A caller may therefore use it only if it also arranges for
-- 'inferSortOf' to be asked of the same type somewhere, and rejects the file if
-- that fails.  \"Front.Lower\" does exactly that under @-jN@; SPEC.md §11.6 has
-- the argument.
assumedSortOf :: Expr -> TC Level
assumedSortOf e = inferM Assume [] e >>= ensureSort

ensureSort :: Expr -> TC Level
ensureSort t = whnf t >>= \case
  Sort l -> pure l
  t'     -> throwTC ("expected a sort, got " ++ showExpr t')

ensurePi :: Expr -> TC (Expr, Expr)
ensurePi t = whnf t >>= \case
  Pi _ dom cod -> pure (dom, cod)
  t'           -> throwTC ("expected a function type, got " ++ showExpr t')

-- | Projection typing.
--
-- @s.i@ requires @s : T params@ for a structure-like @T@, and the type of the
-- field is read off the constructor's telescope with earlier fields replaced by
-- earlier projections of @s@.
--
-- The side condition is the interesting one.  If @T params@ is a proposition
-- then all its inhabitants are convertible, so a projection out of it may only
-- land in a proposition -- otherwise @(mk true).0@ and @(mk false).0@ would be
-- convertible.  Stated over all universe assignments the condition
-- @sortT = 0 -> sortF = 0@ is exactly @sortF <= imax sortF sortT@.
--
-- It applies to the field being projected, and also to every earlier field
-- whose projection actually turns up in the rest of the telescope: reading
-- @s.i@ off a telescope that was instantiated with an /illegal/ projection
-- would be reading it off a type that does not exist.  An earlier field that
-- nothing downstream mentions is simply skipped, so a data field may sit
-- between two proof fields of a proposition without poisoning them.
inferProj :: InferMode -> LEnv -> Name -> Int -> Expr -> TC Expr
inferProj m lenv tn i s0 = do
  env <- getEnv
  when (i < 0) $ throwTC "negative projection index"
  sTy <- inferM m lenv s0 >>= whnf
  -- The field types are built from projections /of this term/, so here it does
  -- have to be materialised.
  s <- closeIn lenv s0
  let (h, args) = unApps sTy
  case h of
    Const tn' ls | tn' == tn -> do
      ind <- lookupConstC tn >>= \case
        Just (CInd ind) -> pure ind
        _               -> throwTC ("projection: " ++ showName tn ++ " is not an inductive type")
      unless (isStructureLike env tn) $
        throwTC ("projection: " ++ showName tn ++ " is not a structure")
      ci <- case indCtors ind of
        [cn] -> lookupConstC cn >>= \case
          Just (CCtor ci) -> pure ci
          _ -> throwTC ("projection: " ++ showName tn ++ " has no unique constructor")
        _ -> throwTC ("projection: " ++ showName tn ++ " has no unique constructor")
      let nps = indNumParams ind
      unless (length args == nps) $
        throwTC ("projection: " ++ showName tn ++ " applied to the wrong number of arguments")
      unless (i < ctorNumFields ci) $
        throwTC ("projection index " ++ show i ++ " out of range for " ++ showName tn)
      cty0 <- instLevels (ctorLevels ci) ls (ctorType ci)
      cty  <- peelParams nps args cty0
      let checkField j fty = when (m == Verify) $ do
            sortT <- ensureSort =<< inferOnly sTy
            sortF <- inferSortOf fty
            unless (levelLeq sortF (LIMax sortF sortT)) $
              throwTC ("projection out of a proposition into " ++ showLevel sortF
                       ++ ": " ++ showName tn ++ "." ++ show j)
          peelFields j ty
            | j == i    = do
                (dom, _) <- ensurePi ty
                checkField i dom
                pure dom
            | otherwise = do
                (dom, cod) <- ensurePi ty
                -- @s.j@ is about to be substituted into the rest of the
                -- telescope; if it actually turns up there then it has to be a
                -- legal projection itself, or the type we finally read off is
                -- built from a term that does not typecheck.
                when (hasLooseBVars cod) (checkField j dom)
                peelFields (j + 1) (inst1 (Proj tn j s) cod)
      peelFields 0 cty
    _ -> throwTC ("projection: expected a value of type " ++ showName tn
                  ++ ", got " ++ showExpr sTy)
  where
    peelParams 0 _ ty = pure ty
    peelParams k ps ty = do
      (_, cod) <- ensurePi ty
      peelParams (k - 1) (tail ps) (inst1 (head ps) cod)
