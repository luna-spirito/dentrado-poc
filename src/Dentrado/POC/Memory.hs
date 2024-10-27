{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE QuantifiedConstraints #-}

module Dentrado.POC.Memory where

import Control.Algebra
import Control.Carrier.Empty.Church (EmptyC)
import Control.Carrier.Lift
import Control.Carrier.Reader (ReaderC, asks, runReader)
import Control.Carrier.State.Church (StateC)
import Control.Carrier.Writer.Church (Writer, WriterC, runWriter)
import Control.Effect.Empty (Empty, empty)
import qualified Control.Effect.Empty as E
import Control.Effect.Fresh (Fresh (..), fresh)
import Control.Effect.Reader (Reader, ask)
import Control.Effect.State (State, get, put)
import Control.Effect.Sum (Member, inj)
import Control.Effect.Writer (tell)
import Data.Bits (finiteBitSize, unsafeShiftL, unsafeShiftR, (.|.))
import qualified Data.ByteString as B
import qualified Data.ByteString.Builder as B
import Data.ByteString.Unsafe as B
import Data.Constraint (Dict (..), withDict)
import Data.Dynamic (Dynamic, fromDynamic)
import Data.Functor.Compose (Compose (..))
import qualified Data.IntMap.Strict as IMap
import Data.Kind (Type)
import Data.Tuple (swap)
import Data.Type.Equality (type (~))
import Dentrado.POC.TH (moduleId, sFreshI)
import Dentrado.POC.Types (Any1 (..), Dynamic1 (..), Event, EventId, LocalEventId, MapDiffE, RadixChunk', RadixTree, Reducible (..), SiteAccessLevel, StateGraphEntry, Timestamp, fromEmpty, maybeToEmpty, readReducible)
import GHC.Base (Symbol)
import GHC.Exts (IsList (..))
import qualified GHC.Generics as G
import RIO hiding (Reader, ask, asks, catch, mask, runReader, toList)
import RIO.List (uncons)
import qualified RIO.List as L
import qualified RIO.Partial as P
import System.IO.Unsafe (unsafePerformIO)
import System.Mem.Weak (Weak, deRefWeak, mkWeakPtr)
import Type.Reflection (eqTypeRep, pattern TypeRep, type (:~~:) (..))
import qualified Type.Reflection as T
import Unsafe.Coerce (unsafeCoerce)

{-
Memory module is responsible for serialization-related definitions.
It defines and implements `Ser` class/interface/trait to perform serialization and implements
it for a number of types.

It also defines Gear (reactive cell), Res and execution evironment.

NOTE: right now Dentrado is memory-only, disk persistence is not actually implemented.
-}

$(moduleId 0)

-- TODO: remove Typeable checks?..
-- TODO: SecureIO instead of IO, a top-level monad that catches IO errors
-- TODO: cleanup funcs

-- Utils

newtype RevList a = UnsafeRevList [a] deriving (Functor)

instance Semigroup (RevList a) where
  UnsafeRevList a <> UnsafeRevList b = UnsafeRevList $ b <> a
instance Monoid (RevList a) where
  mempty = []

revSnoc ∷ RevList a → a → RevList a
revSnoc (UnsafeRevList ls) x = UnsafeRevList $ x : ls

revUnsnoc ∷ RevList a → Maybe (RevList a, a)
revUnsnoc (UnsafeRevList x) = (\(v, l) → (UnsafeRevList l, v)) <$> uncons x

instance IsList (RevList a) where
  type Item (RevList a) = a
  fromList ls = UnsafeRevList $ reverse ls
  toList (UnsafeRevList ls) = reverse ls

{- | `tryLazy` is an utility function that is used to access lazy value.
It tries to extract `b` from value `a` right away, and, if this fails, it updates `a` according to the provided
function and returns the computed result.
-}
tryLazy ∷ (MonadUnliftIO m) ⇒ MVar a → (a → m (Either b (m (a, b)))) → m b
tryLazy xV f = do
  xTry ← readMVar xV
  f xTry >>= \case
    Left res → pure res
    Right _ → modifyMVar xV \x →
      f x >>= \case
        Left res → pure (x, res)
        Right act → act

-- Resources

{- | Wrapper for builtin resources.
`ResB` contains the value along the constant unique identifier, typically acquired via $sFreshI (see Dentrado.POC.TH).
-}
data ResB a = ResB !Word64 {- no bang -} a

{- | Allocated resource. This is a resource produced by `alloc` a runtime value at some point in the past.
ResA might not contain the resource, and instead hold the reference to it on the disk.
-}
data ResA a
  = (Ser a) ⇒ ResNew !a -- Ser to serialize, since serialization is a background job
  | ResUnloaded !Word64
  | ResLoaded !Word64 !a

-- | Res = ResB + ResA
data Res a
  = ResBuiltin !(ResB a)
  | ResAlloc !(MVar (ResA a))

-- Env

-- | Computation provided by the external system to load elements from the disk.
newtype EnvLoad = EnvLoad (∀ a. (Ser a) ⇒ Word64 → IO a)

-- | Computation provided by the external system to store elements to the disk.
newtype EnvStore = EnvStore (∀ a. (Ser a) ⇒ a → IO Word64)

-- Note: currently both methods are not implemented and just throw an exception.

-- TODO?: replace with RadixTree

-- | Execution envronment.
data Env = Env
  { envFreshInd ∷ !(IORef Int) -- TODO: POC: This field currently store the next fresh identifier for allocated resource.
  -- In the actual implementation, it should be provided by the external system (EnvStore).
  , envBuiltins ∷ !(IntMap Dynamic) -- Dictionary of builtin operations. Allows to deserialize ResB.
  , envKnown ∷ !(MVar (IntMap (Weak (Dynamic1 Res)))) -- Known resources. Might not even be actually loaded.
  -- This is a centralized storage that ensures that, if some object is loaded by independent systems,
  -- only one copy is actually stored. Is it also possibly? used to keep track of in-memory resources
  -- and to save them to disk in background.
  , -- TODO: contention-free
    envLoad ∷ !EnvLoad
  , envStore ∷ !EnvStore
  , envGearsIndex ∷ !(MVar (RadixTree Res SerializedGearFn Int)) -- index of initialized Gears (reactive cells).
  -- Whenever a new gear is initialized from a GearTemplate, the instantiation is saved here to ensure some degree of deduplication.
  -- Stores Int identifier of the storage cell provided for the Gear.
  , envGears ∷ !(MVar (IntMap Dynamic)) -- List of storage cells for Gears.
  , envEvents ∷ !(MVar (RevList (EventId, Any1 Val), Int)) -- List of all currently known events.
  }

{-
TODO: envGearsIndex; In the future, we'll need to implement deduplication mechanism.
However, putting deduplicatable entities (those that contain Res) *as keys* of the RadixTree breaks a lot.
We'll either have to teach the deduplicator handle RadixTree, or we invent something stupid to make sure that those Res are left alone
and not affected by the deduplicator.
For the time being, we'll consider deduplicator a non-existant concept.
-}

-- | AppIOC = Env + IO context
newtype AppIOC a = AppIOC {unAppIOC ∷ ReaderC Env IO a}
  deriving (Functor, Applicative, Monad, MonadIO, MonadUnliftIO)

type AppIO = Lift AppIOC :+: Reader Env

instance Algebra AppIO AppIOC where
  alg hdl sig ctx = case sig of
    L (LiftWith f) → f hdl ctx
    R other → AppIOC $ alg (unAppIOC . hdl) (inj other) ctx

sendAI ∷ (Has AppIO sig m) ⇒ AppIOC a → m a
sendAI = sendM
{-# INLINE sendAI #-}

-- Serialization

{- | Data type that is used to identify what resources are being referenced by certain Res.
Currently any Res is only allowed to reference other Res.
TODO: Track gears & events & ... & other external objects as Obj
-}
data Obj r
  = ObjRes !r

-- | ObjExt !Word64 !ByteString -- I can't handle this at the moment.
data Consume e (m ∷ Type → Type) a where
  Consume ∷ Consume e m e

consume ∷ (Has (Consume e) sig m) ⇒ m e
consume = send Consume
{-# INLINE consume #-}

newtype ConsumeC e m a = ConsumeC {unConsumeC ∷ StateC [e] m a}
  deriving (Functor, Applicative, Monad)

instance (Algebra sig m, Member Empty sig) ⇒ Algebra (Consume e :+: sig) (ConsumeC e m) where
  alg hdl sig ctx = ConsumeC case sig of
    L Consume → do
      oldList ← get
      (x, xs) ← maybeToEmpty $ uncons oldList
      put xs
      pure $ ctx $> x
    R other → alg (unConsumeC . hdl) (R other) ctx

type SerM = WriterC Builder AppIOC
type DeserM = StateC ByteString (EmptyC AppIOC)

{- | Serialization class.
This class is used to serialize/deserialize objects.
Typeable: not required, but I see no reason not to include it here, because this requirement appears everywhere.
-}
class (Typeable a) ⇒ Ser a where
  -- | Serialize the object of type `a`. Returns the ByteString of the object along with list of objects that it references.
  ser ∷ a → WriterC (RevList (Obj (Any1 Res))) SerM ()

  -- | Deserialize the object of type `a`. Accepts the ByteString of the object along with the list of objects that it references.
  deser ∷ ConsumeC (Obj Word64) DeserM a

  default ser ∷ (Generic a, GSer (G.Rep a)) ⇒ a → WriterC (RevList (Obj (Any1 Res))) SerM ()
  ser = gSer . G.from

  default deser ∷ (Generic a, GSer (G.Rep a)) ⇒ ConsumeC (Obj Word64) DeserM a
  deser = G.to <$> gDeser

-- Force serialization of the object and acquire its identifier.
-- TODO: Remove if possible.
getInd ∷ Res a → AppIOC Word64
getInd = \case
  ResBuiltin (ResB i _) → pure i
  ResAlloc xV → do
    EnvStore store ← asks envStore
    sendAI $ tryLazy xV $ pure . \case
      ResUnloaded i → Left i
      ResLoaded i _ → Left i
      ResNew o → Right do
        i ← liftIO $ store o
        pure (ResLoaded i o, i)

putWord8 ∷ (Has (Writer Builder) sig m) ⇒ Word8 → m ()
putWord8 = tell . B.word8

getWord8 ∷ (Has (State ByteString :+: Empty) sig m) ⇒ m Word8
getWord8 = do
  old ← get
  (x, new) ← maybeToEmpty $ B.uncons old
  put new
  pure x

-- Serialization of ResB is performed just by instructing the system to store the pointer.
-- Pointer serialization is queued and is not performed instantly, since that would require to
-- force serialization of the referenced object.
instance (Typeable a) ⇒ Ser (ResB a) where
  ser x = tell @(RevList (Obj (Any1 Res))) [ObjRes $ Any1 $ ResBuiltin x]
  deser = do
    addr ∷ Word64 ←
      consume >>= \case
        ObjRes addr → pure addr
        _notRes → empty
    builtins ← asks envBuiltins
    pure $ ResB addr $ P.fromJust $ fromDynamic $ P.fromJust $ IMap.lookup (fromIntegral addr) builtins -- TODO-post-POC

-- Serialize/deserialize (Res a).
-- On deserialization, accesses global `envKnown` store to ensure that
-- some object is stored only once in memory.
instance (Typeable a) ⇒ Ser (Res a) where
  ser x = tell @(RevList (Obj (Any1 Res))) [ObjRes $ Any1 x]
  deser = do
    addr ∷ Word64 ←
      consume >>= \case
        ObjRes addr → pure addr
        _notRes → empty
    if (addr `unsafeShiftR` (finiteBitSize addr - 1)) == 1
      then do
        builtins ← asks envBuiltins
        pure $ ResBuiltin $ ResB addr $ P.fromJust $ fromDynamic $ P.fromJust $ IMap.lookup (fromIntegral addr) builtins -- TODO-post-POC
      else do
        -- TODO: move to Ser (ResA a)
        knownM ← asks envKnown
        let cleanupAddr =
              modifyMVar_ knownM
                $ IMap.alterF
                  ( \val → do
                      alive ← maybe (pure False) (fmap isJust . deRefWeak) val
                      pure $ guard alive *> val
                  )
                  (fromIntegral addr)
        sendAI $ liftIO $ modifyMVar knownM \oldKnown →
          swap
            <$> getCompose
              ( IMap.alterF
                  ( Compose . \existingWeak → do
                      existingM ← maybe (pure Nothing) deRefWeak existingWeak
                      case existingM of
                        Nothing → do
                          new ← ResAlloc <$> newMVar (ResUnloaded addr)
                          (new,) . Just <$> mkWeakPtr (Dynamic1 TypeRep new) (Just cleanupAddr)
                        Just (Dynamic1 t2 existing) →
                          (,existingWeak) <$> do
                            Just HRefl ← pure $ eqTypeRep (TypeRep @a) t2 -- TODO-post-POC: invent something to deal with this failure
                            pure existing
                  )
                  (fromIntegral addr)
                  oldKnown
              )

instance Ser ()
instance (Ser a, Ser b) ⇒ Ser (a, b) where
  ser (a, b) = ser a *> ser b
  deser = (,) <$> deser <*> deser

instance Ser Word8 where
  ser = putWord8
  deser = getWord8
instance Ser Bool where
  ser =
    putWord8 . \case
      False → 0
      True → 1
  deser =
    getWord8 <&> \case
      0 → False
      _1 → True
instance Ser Word32 where
  ser = tell . B.word32BE
  deser = do
    old ← get
    E.guard (B.length old >= 4)
    put $ B.drop 4 old
    -- https://hackage.haskell.org/package/cereal-0.5.8.3/docs/src/Data.Serialize.Get.html#getWord32be
    pure
      $ (fromIntegral @_ @Word32 (old `B.unsafeIndex` 0) `unsafeShiftL` 24)
      .|. (fromIntegral @_ @Word32 (old `B.unsafeIndex` 1) `unsafeShiftL` 16)
      .|. (fromIntegral @_ @Word32 (old `B.unsafeIndex` 2) `unsafeShiftL` 8)
      .|. fromIntegral @_ @Word32 (old `B.unsafeIndex` 3)
instance Ser Word64 where
  ser = tell . B.word64BE
  deser = do
    old ← get
    E.guard (B.length old >= 8)
    put $ B.drop 8 old
    return $! (fromIntegral (old `B.unsafeIndex` 0) `unsafeShiftL` 56)
      .|. (fromIntegral (old `B.unsafeIndex` 1) `unsafeShiftL` 48)
      .|. (fromIntegral (old `B.unsafeIndex` 2) `unsafeShiftL` 40)
      .|. (fromIntegral (old `B.unsafeIndex` 3) `unsafeShiftL` 32)
      .|. (fromIntegral (old `B.unsafeIndex` 4) `unsafeShiftL` 24)
      .|. (fromIntegral (old `B.unsafeIndex` 5) `unsafeShiftL` 16)
      .|. (fromIntegral (old `B.unsafeIndex` 6) `unsafeShiftL` 8)
      .|. (fromIntegral (old `B.unsafeIndex` 7))

-- Hope this won't backfire...
-- TODO: Redo with varint
instance Ser Int where
  ser = ser @Word64 . fromIntegral
  deser = fromIntegral <$> deser @Word64

instance (Ser a) ⇒ Ser (Maybe a)
instance (Ser a) ⇒ Ser [a] where
  ser l = ser (L.length l) *> for_ l ser

instance Ser Text where
  ser a =
    let encoded = encodeUtf8 a
     in ser (B.length encoded) *> tell (B.byteString encoded)
  deser = do
    l ∷ Int ← deser
    old ← get
    put $ B.drop l old
    either (const E.empty) pure $ decodeUtf8' $ B.take l old

instance (Container c, Ser a, Typeable c, Typeable k) ⇒ Ser (RadixTree c k a)
instance (Container c, Ser a, Typeable c, Typeable k) ⇒ Ser (RadixChunk' c k a)
instance (Ser a) ⇒ Ser (MapDiffE a)

-- POC stuff
instance (Ser v) ⇒ Ser (StateGraphEntry v)
instance Ser Timestamp
instance Ser LocalEventId
instance Ser EventId

instance Ser SiteAccessLevel
instance Ser Event

-- GSer
-- The following code is just a boilerplate for Haskell to automatically derive Ser class/trait/interface
-- implementation for any regular data type.

class GSer (f ∷ k → Type) where
  gSer ∷ f x → WriterC (RevList (Obj (Any1 Res))) SerM ()
  gDeser ∷ ConsumeC (Obj Word64) DeserM (f x) -- probably better to encapsulate

class GSerSum (f ∷ k → Type) where
  gSerSum ∷ Int → f x → WriterC (RevList (Obj (Any1 Res))) SerM ()
  gDeserSum ∷ Int → ConsumeC (Obj Word64) DeserM (f x)

class GSumSize (f ∷ k → Type) where
  sumSize ∷ Proxy f → Int

instance (GSumSize a, GSumSize b) ⇒ GSumSize (a G.:+: b) where
  sumSize _ = sumSize (Proxy @a) + sumSize (Proxy @b)
instance GSumSize (a G.:*: b) where
  sumSize _ = 1
instance (GSumSize a) ⇒ GSumSize (G.M1 i c a) where
  sumSize _ = sumSize (Proxy @a)
instance GSumSize (G.K1 i a) where
  sumSize _ = 1
instance GSumSize G.U1 where
  sumSize _ = 1

instance (GSumSize a, GSerSum a, GSerSum b) ⇒ GSerSum (a G.:+: b) where
  gSerSum i = \case
    G.L1 l → gSerSum i l
    G.R1 r → gSerSum (i + sumSize (Proxy @a)) r
  gDeserSum i =
    if i >= sumSize (Proxy @a)
      then G.R1 <$> gDeserSum (i - sumSize (Proxy @a))
      else G.L1 <$> gDeserSum i
gSerSum_ ∷ ∀ k (f ∷ k → Type) x. (GSer f) ⇒ Int → f x → WriterC (RevList (Obj (Any1 Res))) SerM ()
gSerSum_ i v = putWord8 (fromIntegral i) *> gSer v
gDeserSum_ ∷ ∀ k (f ∷ k → Type) x. (GSer f) ⇒ Int → ConsumeC (Obj Word64) DeserM (f x)
gDeserSum_ = \case
  0 → error "invalid fresh"
  _ → gDeser
instance (GSer (a G.:*: b)) ⇒ GSerSum (a G.:*: b) where
  gSerSum = gSerSum_
  gDeserSum = gDeserSum_
instance (GSerSum a) ⇒ GSerSum (G.M1 i c a) where
  gSerSum i = gSerSum i . G.unM1
  gDeserSum i = G.M1 <$> gDeserSum i
instance (GSer (G.K1 c a ∷ k → Type)) ⇒ GSerSum (G.K1 c a ∷ k → Type) where
  gSerSum = gSerSum_
  gDeserSum = gDeserSum_
instance GSerSum G.U1 where
  gSerSum = gSerSum_
  gDeserSum = gDeserSum_

instance (GSerSum (a G.:+: b)) ⇒ GSer (a G.:+: b) where
  gSer = gSerSum 0
  gDeser = do
    i ← getWord8
    gDeserSum (fromIntegral i)
instance (GSer a, GSer b) ⇒ GSer (a G.:*: b) where
  gSer (a G.:*: b) = gSer a *> gSer b
  gDeser = do
    i ← getWord8
    gDeserSum (fromIntegral i)
instance (GSer a) ⇒ GSer (G.M1 i c a) where
  gSer = gSer . G.unM1
  gDeser = G.M1 <$> gDeser
instance (Ser a) ⇒ GSer (G.K1 i a) where
  gSer (G.K1 a) = ser a
  gDeser = G.K1 <$> deser
instance GSer G.U1 where
  gSer G.U1 = pure ()
  gDeser = pure G.U1

-- Reduce
-- Reducible-related functionality. Optimization, could be omitted.

data Reduce' (s ∷ Symbol) (m ∷ Type → Type) a where
  GetReduce' ∷ Reduce' s m (IORef Bool)
newtype Reduce'C (s ∷ Symbol) m a = Reduce'C (ReaderC (IORef Bool) m a)
  deriving (Functor, Applicative, Monad, MonadTrans)

instance (Algebra sig m) ⇒ Algebra (Reduce' s :+: sig) (Reduce'C s m) where
  alg hdl sig ctx = Reduce'C $ case sig of
    L GetReduce' → (ctx $>) <$> ask
    R r → alg ((\(Reduce'C x) → x) . hdl) (R r) ctx
  {-# INLINE alg #-}
type Reduce = Reduce' ""
type ReduceC = Reduce'C ""

runReduce' ∷ ∀ s sig m a. (Has AppIO sig m) ⇒ Reduce'C s m a → m a
runReduce' (Reduce'C act) = do
  flag ← sendAI $ newIORef False
  runReader flag act
{-# INLINE runReduce' #-}

runReduce ∷ ∀ sig m a. (Has AppIO sig m) ⇒ ReduceC m a → m a
runReduce = runReduce' @""
{-# INLINE runReduce #-}

catchReduce ∷ (Has (AppIO :+: Reduce' s) sig m) ⇒ Proxy s → m a → Reduce'C s AppIOC () → m a
catchReduce (Proxy @s) act onReduce = do
  flag ← send $ GetReduce' @s
  liftWith @AppIOC \hdl ctx → do
    let orig `overwriteWith` new = when (orig /= new) $ sendAI $ writeIORef flag new
    outerVal ← sendAI $ readIORef flag
    outerVal `overwriteWith` False
    res ← hdl (ctx $> act)
    innerVal ← sendAI $ readIORef flag
    innerVal `overwriteWith` outerVal
    when innerVal
      $ let (Reduce'C redAct) = onReduce
         in runReader flag redAct
    pure res
{-# INLINE catchReduce #-}

reduce' ∷ (Has (AppIO :+: Reduce' s) sig m) ⇒ Proxy s → m ()
reduce' (Proxy @s) = do
  flag ← send $ GetReduce' @s
  sendAI $ writeIORef flag True

instance (Ser a) ⇒ Ser (Reducible a) where
  ser = ser . readReducible
  deser = mkReducible <$> deser

mkReducible ∷ a → Reducible a
mkReducible = Reducible . unsafePerformIO . newIORef

reducible' ∷ (Has (AppIO :+: Reduce' s) sig m) ⇒ Proxy s → (a → Reduce'C s AppIOC a) → Reducible a → (a → m b) → m b
reducible' proxy reductor (Reducible red) f = do
  orig ← sendAI $ readIORef red
  catchReduce
    proxy
    (f orig)
    do
      newValue ← reductor orig
      sendAI $ writeIORef red newValue
{-# INLINE reducible' #-}

reducible ∷ (Has (AppIO :+: Reduce) sig m) ⇒ (a → ReduceC AppIOC a) → Reducible a → (a → m b) → m b
reducible = reducible' (Proxy @"")
{-# INLINE reducible #-}

-- Values and functions

infixr 1 :->

{- | Serializable function. Currently this is just a glorified wrapper over `ResB (a -> b)`
(i. e. a wrapper over a builtin function from `a` to `b`)
However, in future this could be greatly extended to support any lambda calculus expressions.
-}
data a :-> b where
  FunBuiltin ∷ !(ResB (a → b)) → a :-> b
  FunCurry ∷ ((a, b) :-> c) → a :-> b :-> c
  FunCurry1 {-no bang-} ∷ ValT a → !a → !((a, b) :-> c) → b :-> c

-- TODO: maybe unsafes could be cleaned by... uh... Res (c a) ~ Res (Any1 c)? well, implement Res in a way that it allows deserialized data to itself say the type.

-- (:->) serialization/deserialization
instance (Typeable a, Typeable b) ⇒ Ser (a :-> b) where
  ser = \case
    FunBuiltin x → putWord8 0 *> ser x
    FunCurry f → case TypeRep @b of
      arr `T.App` TypeRep `T.App` TypeRep
        | Just HRefl ← eqTypeRep arr (TypeRep @(:->)) →
            putWord8 1 *> ser f
      _imp → error "impossible"
    FunCurry1 xT@(valSerProof → Dict) x f → putWord8 2 *> ser (Any1 (Val xT x)) *> ser f
  deser =
    getWord8 >>= \case
      0 → FunBuiltin <$> deser
      1 → case TypeRep @b of
        arr `T.App` TypeRep `T.App` TypeRep
          | Just HRefl ← eqTypeRep arr (TypeRep @(:->)) →
              FunCurry <$> deser
        _err → empty
      _2 → do
        Any1 (Val xT@(valSerProof → Dict) x) ← deser
        FunCurry1 xT x <$> deser

-- | Use :-> as regular function.
funApp ∷ (InferValT a) ⇒ a :-> b → a → b
funApp = funApp' inferValT

-- | Turn constant function into :->
builtinFun ∷ (Has Fresh sig m) ⇒ (a → b) → m (a :-> b)
builtinFun f = FunBuiltin <$> builtin f

builtinFunM ∷ (Has Fresh sig m) ⇒ (a → f b) → m (a :-> M f b)
builtinFunM f = builtinFun (M . f)

funApp' ∷ ValT a → (a :-> b) → a → b
funApp' xT f x = case f of
  FunBuiltin (ResB _ f') → f' x
  FunCurry f' → FunCurry1 xT x f'
  FunCurry1 aT a f' → funApp' (ValTTuple aT xT) f' (a, x)

--

{-
Dentrado doesn't have any scheme and could store data of any type in any cell.
Typically the type of the accessed cell is inferred from the context.
However, this is not always possible, and sometimes we need to store the type of data
along the data on the disk.

TODO: Currently only builtin types are supported. This should be fixed soon.
-}

-- | Type of monadic computation.
data MonadT m where
  MonadTAppIOC ∷ MonadT AppIOC
  MonadTReduceC ∷ MonadT m → MonadT (ReduceC m)
  MonadTReduceC1 ∷ MonadT m → MonadT (Reduce'C "1" m)
  MonadTReduceC2 ∷ MonadT m → MonadT (Reduce'C "2" m)

-- | Boilerplate for Haskell to inference the type to store.
class InferMonadT m where
  inferMonadT ∷ MonadT m

instance InferMonadT AppIOC where
  inferMonadT = MonadTAppIOC
instance (InferMonadT m) ⇒ InferMonadT (ReduceC m) where
  inferMonadT = MonadTReduceC inferMonadT
instance (InferMonadT m) ⇒ InferMonadT (Reduce'C "1" m) where
  inferMonadT = MonadTReduceC1 inferMonadT
instance (InferMonadT m) ⇒ InferMonadT (Reduce'C "2" m) where
  inferMonadT = MonadTReduceC2 inferMonadT

-- Serialize the type.
instance Ser (Any1 MonadT) where
  ser (Any1 x) = case x of
    MonadTAppIOC → putWord8 0
    MonadTReduceC y → putWord8 1 *> ser (Any1 y)
    MonadTReduceC1 y → putWord8 2 *> ser (Any1 y)
    MonadTReduceC2 y → putWord8 3 *> ser (Any1 y)
  deser =
    getWord8 >>= \case
      0 → pure $ Any1 MonadTAppIOC
      1 → (\(Any1 x) → Any1 $ MonadTReduceC x) <$> deser
      2 → (\(Any1 x) → Any1 $ MonadTReduceC1 x) <$> deser
      _3 → (\(Any1 x) → Any1 $ MonadTReduceC2 x) <$> deser

-- | Extract information about the stored monad type from MonadT.
monadTypeableProof ∷ MonadT m → Dict (Typeable m)
monadTypeableProof = \case
  MonadTAppIOC → Dict
  MonadTReduceC (monadTypeableProof → Dict) → Dict
  MonadTReduceC1 (monadTypeableProof → Dict) → Dict
  MonadTReduceC2 (monadTypeableProof → Dict) → Dict

--

-- | Container type.
data ContainerT a where
  ContainerTRes ∷ ContainerT Res
  ContainerTDelay ∷ ContainerT Delay

-- | Container type inference.
class InferContainerT a where
  inferContainerT ∷ ContainerT a

instance InferContainerT Res where
  inferContainerT = ContainerTRes
instance InferContainerT Delay where
  inferContainerT = ContainerTDelay

-- | Container type serialization.
instance Ser (Any1 ContainerT) where
  ser (Any1 c) = case c of
    ContainerTRes → putWord8 0
    ContainerTDelay → putWord8 1
  deser =
    getWord8 <&> \case
      0 → Any1 ContainerTRes
      _1 → Any1 ContainerTDelay

-- | Extract information about stored container type from ContainerT.
containerContainerProof ∷ ContainerT a → Dict (Container a)
containerContainerProof = \case
  ContainerTRes → Dict
  ContainerTDelay → Dict

--

-- | No-op wrapper. Used to simplify Haskell type inference.
newtype M m a = M {unM ∷ m a}

-- | No-op wrapper. Used to simplify Haskell type inference.
newtype C c a = C {unC ∷ c a}
  deriving (Ser)

-- | ValT is a value that stores serializable type.
data ValT a where
  ValTFun ∷ !(ValT a) → !(EValT b) → ValT (a :-> b)
  ValTTuple ∷ !(ValT a) → !(ValT b) → ValT (a, b)
  ValTRadixTree ∷ !(ContainerT c) → !(ValT k) → !(ValT v) → ValT (RadixTree c k v)
  ValTContainer ∷ !(ContainerT c) → !(ValT a) → ValT (C c a)
  ValTMaybe ∷ !(ValT a) → ValT (Maybe a)
  ValTReducible ∷ !(ValT a) → ValT (Reducible a)
  ValTRadixChunk ∷ !(ContainerT c) → !(ValT k) → !(ValT v) → ValT (RadixChunk' c k v)
  ValTEvent ∷ ValT Event -- should not be here, but tolerable for POC
  ValTMapDiffE ∷ ValT a → ValT (MapDiffE a)
  ValTUnit ∷ ValT ()
  ValTInt ∷ ValT Int
  ValTEventId ∷ ValT EventId
  ValTGear ∷ ValT ctx → EValT out → ValT (Gear ctx out)
  ValTWord32 ∷ ValT Word32
  -- ValTValGear :: ValT ctx -> ValT (ValGear ctx)
  ValTList ∷ ValT a → ValT [a]
  ValTStateGraphEntry ∷ ValT a → ValT (StateGraphEntry a)
  ValTSiteAccessLevel ∷ ValT SiteAccessLevel

{- |
EValT is an ephemeral extension of ValT. It includes types that cannot be easily serialized.
One typical case for EValT to appear is as the right hand of an :-> arrow.
This refers to a computation that produces a non-serializable result (like a monad).
-}
data EValT a where
  EValT {-Lift-} ∷ ValT a → EValT a
  EValTMonad ∷ MonadT m → EValT a → EValT (M m a)

class InferValT a where
  inferValT ∷ ValT a
instance (InferValT a, InferEValT b) ⇒ InferValT (a :-> b) where
  inferValT = ValTFun inferValT inferEValT
instance (InferValT a, InferValT b) ⇒ InferValT (a, b) where
  inferValT = ValTTuple inferValT inferValT
instance (InferContainerT c, InferValT k, InferValT v) ⇒ InferValT (RadixTree c k v) where
  inferValT = ValTRadixTree inferContainerT inferValT inferValT
instance (InferContainerT c, InferValT v) ⇒ InferValT (C c v) where
  inferValT = ValTContainer inferContainerT inferValT
instance (InferValT a) ⇒ InferValT (Maybe a) where
  inferValT = ValTMaybe inferValT
instance (InferValT a) ⇒ InferValT (Reducible a) where
  inferValT = ValTReducible inferValT
instance (InferContainerT c, InferValT k, InferValT v) ⇒ InferValT (RadixChunk' c k v) where
  inferValT = ValTRadixChunk inferContainerT inferValT inferValT
instance InferValT Event where
  inferValT = ValTEvent
instance (InferValT a) ⇒ InferValT (MapDiffE a) where
  inferValT = ValTMapDiffE inferValT
instance InferValT () where
  inferValT = ValTUnit
instance InferValT Int where
  inferValT = ValTInt
instance InferValT EventId where
  inferValT = ValTEventId
instance (InferValT ctx, InferEValT out) ⇒ InferValT (Gear ctx out) where
  inferValT = ValTGear inferValT inferEValT
instance InferValT Word32 where
  inferValT = ValTWord32

-- instance InferValT ctx => InferValT (ValGear ctx) where
--   inferValT = ValTValGear inferValT
instance (InferValT a) ⇒ InferValT [a] where
  inferValT = ValTList inferValT
instance (InferValT a) ⇒ InferValT (StateGraphEntry a) where
  inferValT = ValTStateGraphEntry inferValT
instance InferValT SiteAccessLevel where
  inferValT = ValTSiteAccessLevel

class InferEValT a where
  inferEValT ∷ EValT a
instance {-# OVERLAPPABLE #-} (InferValT a) ⇒ InferEValT a where
  inferEValT = EValT inferValT
instance (InferMonadT m, InferEValT a) ⇒ InferEValT (M m a) where
  inferEValT = EValTMonad inferMonadT inferEValT

valSerProof ∷ ValT x → Dict (Ser x)
valSerProof = \case
  ValTFun (valSerProof → Dict) (evalTypeableProof → Dict) → Dict
  ValTTuple (valSerProof → Dict) (valSerProof → Dict) → Dict
  ValTRadixTree (containerContainerProof → Dict) (valSerProof → Dict) (valSerProof → Dict) → Dict
  ValTContainer (containerContainerProof → Dict) (valSerProof → Dict) → Dict
  ValTMaybe (valSerProof → Dict) → Dict
  ValTReducible (valSerProof → Dict) → Dict
  ValTRadixChunk (containerContainerProof → Dict) (valSerProof → Dict) (valSerProof → Dict) → Dict
  ValTEvent → Dict
  ValTMapDiffE (valSerProof → Dict) → Dict
  ValTUnit → Dict
  ValTInt → Dict
  ValTEventId → Dict
  ValTGear (valSerProof → Dict) (evalTypeableProof → Dict) → Dict
  ValTWord32 → Dict
  -- ValTValGear (valSerProof -> Dict) -> Dict
  ValTList (valSerProof → Dict) → Dict
  ValTStateGraphEntry (valSerProof → Dict) → Dict
  ValTSiteAccessLevel → Dict

evalTypeableProof ∷ EValT x → Dict (Typeable x)
evalTypeableProof = \case
  EValT (valSerProof → Dict) → Dict
  EValTMonad (monadTypeableProof → Dict) (evalTypeableProof → Dict) → Dict

deserValT ∷ Word8 → ConsumeC (Obj Word64) DeserM (Any1 ValT)
deserValT = \case
  0 → do
    Any1 a ← deser
    Any1 b ← deser
    pure $ Any1 $ ValTFun a b
  1 → do
    Any1 a ← deser
    Any1 b ← deser
    pure $ Any1 $ ValTTuple a b
  2 → do
    Any1 c ← deser
    Any1 k ← deser
    Any1 v ← deser
    pure $ Any1 $ ValTRadixTree c k v
  3 → do
    Any1 c ← deser
    Any1 v ← deser
    pure $ Any1 $ ValTContainer c v
  4 → do
    Any1 a ← deser
    pure $ Any1 $ ValTMaybe a
  5 → do
    Any1 a ← deser
    pure $ Any1 $ ValTReducible a
  6 → do
    Any1 c ← deser
    Any1 k ← deser
    Any1 v ← deser
    pure $ Any1 $ ValTRadixChunk c k v
  7 → pure $ Any1 ValTEvent
  8 → do
    Any1 a ← deser
    pure $ Any1 $ ValTMapDiffE a
  9 → pure $ Any1 ValTUnit
  10 → pure $ Any1 ValTInt
  11 → pure $ Any1 ValTEventId
  12 → do
    Any1 ctx ← deser
    Any1 out ← deser
    pure $ Any1 $ ValTGear ctx out
  13 → pure $ Any1 ValTWord32
  -- 14 -> do
  --   Any1 ctx <- deser
  --   pure $ Any1 $ ValTValGear ctx
  15 → do
    Any1 a ← deser
    pure $ Any1 $ ValTList a
  16 → do
    Any1 a ← deser
    pure $ Any1 $ ValTStateGraphEntry a
  _17 → do
    pure $ Any1 ValTSiteAccessLevel

-- >= 150 RESERVED FOR EVAL

instance Ser (Any1 ValT) where
  ser (Any1 x) = case x of
    ValTFun a b → putWord8 0 *> ser (Any1 a) *> ser (Any1 b)
    ValTTuple a b → putWord8 1 *> ser (Any1 a) *> ser (Any1 b)
    ValTRadixTree c k v → putWord8 2 *> ser (Any1 c) *> ser (Any1 k) *> ser (Any1 v)
    ValTContainer c v → putWord8 3 *> ser (Any1 c) *> ser (Any1 v)
    ValTMaybe a → putWord8 4 *> ser (Any1 a)
    ValTReducible a → putWord8 5 *> ser (Any1 a)
    ValTRadixChunk c k v → putWord8 6 *> ser (Any1 c) *> ser (Any1 k) *> ser (Any1 v)
    ValTEvent → putWord8 7
    ValTMapDiffE a → putWord8 8 *> ser (Any1 a)
    ValTUnit → putWord8 9
    ValTInt → putWord8 10
    ValTEventId → putWord8 11
    ValTGear ctx out → putWord8 12 *> ser (Any1 ctx) *> ser (Any1 out)
    ValTWord32 → putWord8 13
    -- ValTValGear ctx -> putWord8 14 *> ser (Any1 ctx)
    ValTList a → putWord8 15 *> ser (Any1 a)
    ValTStateGraphEntry a → putWord8 16 *> ser (Any1 a)
    ValTSiteAccessLevel → putWord8 17

  -- >= 150 RESERVED FOR EVal
  deser = getWord8 >>= deserValT

instance Ser (Any1 EValT) where
  ser (Any1 x) = case x of
    EValT a → ser (Any1 a)
    EValTMonad m a → putWord8 150 *> ser (Any1 m) *> ser (Any1 a)
  deser =
    getWord8 >>= \case
      n | n < 150 → do
        Any1 x ← deser
        pure $ Any1 $ EValT x
      _150 → do
        Any1 m ← deser
        Any1 a ← deser
        pure $ Any1 $ EValTMonad m a

-- | Val a = ValT + a
data Val a = Val !(ValT a) !a

-- | EVal a = EValT + a
data EVal a = EVal !(EValT a) !a

-- | Convert Haskell value of type `a` into `Val a`.
asVal ∷ (InferValT a) ⇒ a → Val a
asVal = Val inferValT

-- | Attempt to extract a value of type `a` from `Val` over statically unknown type.
tryFromVal ∷ ∀ a. (Typeable a) ⇒ Any1 Val → Maybe a
tryFromVal (Any1 (Val @b (valSerProof → Dict) a)) =
  (\HRefl → a) <$> eqTypeRep (TypeRep @a) (TypeRep @b)

instance Ser (Any1 Val) where
  ser (Any1 (Val t@(valSerProof → Dict) v)) = ser (Any1 t) *> ser v
  deser = do
    Any1 t@(valSerProof → Dict) ← deser
    Any1 . Val t <$> deser

-- Container (Res/Delay)

-- | Perform "allocation", turning `a` into `Res a`.
alloc ∷ (Has AppIO sig m, Ser a) ⇒ a → m (Res a)
alloc v = ResAlloc <$> sendAI (newMVar $ ResNew v)
{-# INLINE alloc #-}

{- | Perform fetch by loading the value `a` from `Res a`.
This operation potentially causes disk access! (envLoad)
-}
fetch ∷ ∀ sig m a. (Has AppIO sig m, Ser a) ⇒ Res a → m a
fetch = \case
  ResBuiltin (ResB _ v) → pure v
  ResAlloc ref → do
    EnvLoad load ← asks envLoad
    sendAI $ tryLazy ref $ pure . \case
      ResNew v → Left v
      ResLoaded _ v → Left v
      ResUnloaded k → Right do
        v ← liftIO $ load @a k
        pure (ResLoaded k v, v)
{-# INLINE fetch #-}

-- | Attempt to fetch the value without accessing the disk.
tryFetch ∷ Res a → Maybe a
tryFetch = \case
  ResBuiltin (ResB _ v) → Just v
  ResAlloc ref → case unsafePerformIO $ readMVar ref of
    ResNew v → Just v
    ResUnloaded _ → Nothing
    ResLoaded _ v → Just v

-- Interface for Res/Delay. This is used to make it possible to write code generic over the actual used container.
class (∀ a. (Typeable a) ⇒ Ser (t a), Typeable t) ⇒ Container t where
  -- | Any `Res a` can be packaged into a container (Res a => Res a, Res a => Delay a)
  wrap ∷ Res a → t a

  -- | From any container it is possible to extract `Res a` (Res a => Res a, Delay a => Delay a)
  -- This operation is possibly expensive.
  unwrap' ∷ (Has (AppIO :+: Reduce' s) sig m) ⇒ Proxy s → t a → m (Res a)

  -- | Try to quickly extract `Res a` from the container.
  -- Is analogous to unwrap', but fails if the value cannot be instantly returned.
  tryUnwrap ∷ t a → Maybe (Res a)

  -- | Quick comparison of two containers.
  -- Can have false negatives, cannot have false positives.
  -- `same a b = False` is a lawful implementation.
  -- In practice `same` tries to compare two objects by pointer.
  same ∷ t a → t b → Bool

-- | Generalized `alloc`.
allocC ∷ (Container t, Has AppIO sig m, Ser a) ⇒ a → m (t a)
allocC x = wrap <$> alloc x
{-# INLINE allocC #-}

-- | Generalized `unwrap`.
unwrap ∷ (Container c, Has (AppIO :+: Reduce) sig m) ⇒ c a → m (Res a)
unwrap = unwrap' $ Proxy @""

-- | Generalized `tryFetch`.
tryFetchC ∷ (Container c) ⇒ c a → Maybe a
tryFetchC c = tryUnwrap c >>= tryFetch

-- | Generalized fetch.
fetchC' ∷ (Container c, Has (AppIO :+: Reduce' s) sig m, Ser a) ⇒ Proxy s → c a → m a
fetchC' proxy x = fetch =<< unwrap' proxy x
{-# INLINE fetchC' #-}

-- | Generalized fetch.
fetchC ∷ (Container c, Has (AppIO :+: Reduce) sig m, Ser a) ⇒ c a → m a
fetchC = fetchC' (Proxy @"")
{-# INLINE fetchC #-}

instance Container Res where
  wrap = id
  unwrap' _ = pure
  tryUnwrap = Just
  same (ResBuiltin (ResB aId _)) (ResBuiltin (ResB bId _)) = aId == bId
  same (ResAlloc a) (ResAlloc b) = a == unsafeCoerce b
  same _ _ = False

{- | Greedy strategy marker.
This marker is used to identify that some action (such as merge of radix trees) must be performed in a greedy fashion.
-}
data AppForce = AppForce

{- | Delay is a container that is used to store lazily computed values.
When serialized, `Delay` only persists the set of action and not the computed result.
Long Delay chains should be avoided.
-}
data Delay a where
  -- | Any Res is a Delay.
  DelayPin ∷ !(Res a) → Delay a
  -- | Lazy generation of Delay. Is used, for example, to lazily convert Res tree into a Delay tree.
  -- Not persisted.
  DelayLazy ∷
    !(IORef (Either (Delay a) (AppIOC (Delay a)))) →
    -- | TODO: ?, also, it's additional undesirable indirection.
    -- Probably should get moved? Delay a --> Delay' a, Delay a = DelayLazy a + Delay' a
    Delay a
  -- | Actual delayed computation. Is encoded in a tree of DelayApp. Cached after being ran once.
  DelayCache ∷ !(DelayApp (M AppIOC (C Res a))) → !(IORef (Maybe (Res a))) → Delay a

-- | `DelayApp a` is a tree that stores the queue of all operations to apply lazily.
data DelayApp a where
  -- | The function we apply.
  DelayAppUnsafeFun ∷ !(Res (Any1 Val {- typeOf val ~ a -})) → DelayApp a
  -- | Application of the function.
  DelayApp ∷ !(DelayApp (C Res a :-> b)) → !(Delay a) → DelayApp b

-- we could store (DelayApp a) as the second argument, but I believe this interface is good enough

mkDelayCache ∷ (Has AppIO sig m) ⇒ DelayApp (M AppIOC (C Res a)) → m (Delay a)
mkDelayCache x = DelayCache x <$> sendAI (newIORef Nothing)

delayCache ∷ (Has (AppIO :+: Reduce' s) sig m) ⇒ Proxy s → DelayApp (M AppIOC (C Res a)) → IORef (Maybe (Res a)) → m (Res a)
delayCache (Proxy @s) actM memo =
  sendAI (readIORef memo) >>= \case
    Just res → pure res
    Nothing → do
      reduce' (Proxy @s)
      M act ← delayAppVal (Proxy @s) actM
      C res ← sendM act
      sendAI $ writeIORef memo (Just res)
      pure res

withUnsafeEq ∷ ∀ a b x. ((a ~ b) ⇒ x) → x
withUnsafeEq = withDict (unsafeCoerce @() @(Dict (a ~ b)) ())

delayAppVal ∷ ∀ sig m s x. (Has (AppIO :+: Reduce' s) sig m) ⇒ Proxy s → DelayApp x → m x
delayAppVal proxy = fmap (\(EVal _ x) → x) . delayAppVal'
 where
  delayAppVal' ∷ ∀ y. DelayApp y → m (EVal y)
  delayAppVal' = \case
    DelayAppUnsafeFun f → do
      Any1 @_ @a (Val vT v) ← fetchC' proxy f
      pure $ withUnsafeEq @a @y $ EVal (EValT vT) v
    DelayApp (f ∷ DelayApp (C Res a :-> y)) a →
      delayAppVal' f >>= \case
        EVal (EValT (ValTFun aT@(valSerProof → Dict) bT)) f' →
          EVal bT . funApp' aT f' . C <$> unwrap' proxy a

mkDelayLazy ∷ AppIOC (Delay a) → Delay a
mkDelayLazy = DelayLazy . unsafePerformIO . newIORef . Right

unDelayLazy ∷ (Has (AppIO :+: Reduce' s) sig m) ⇒ Proxy s → IORef (Either (Delay a) (AppIOC (Delay a))) → m (Delay a)
unDelayLazy (Proxy @s) ref =
  sendAI (readIORef ref) >>= \case
    Left a → pure a
    Right aM → do
      reduce' (Proxy @s)
      a ← sendAI aM
      sendAI $ writeIORef ref (Left a)
      pure a

instance Container Delay where
  wrap = DelayPin
  unwrap' proxy = \case
    DelayPin x → pure x
    DelayLazy x → unDelayLazy proxy x >>= unwrap' proxy
    DelayCache actM memo → delayCache proxy actM memo
  tryUnwrap = \case
    DelayPin x → Just x
    DelayLazy ref →
      unsafePerformIO (readIORef ref) & \case
        Left v → tryUnwrap v
        Right _ → Nothing
    DelayCache _actM memo → unsafePerformIO (readIORef memo)

  -- \| Comparison of Delay's is performed by deep comparison of the queued operations tree.
  same = curry \case
    (DelayPin a, DelayPin b) → a `same` b
    (DelayCache valM1 memo1, DelayCache valM2 memo2) →
      unsafePerformIO
        ( fromEmpty False do
            m1 ← maybeToEmpty =<< readIORef memo1
            m2 ← maybeToEmpty =<< readIORef memo2
            pure $ m1 `same` m2
        )
        || (valM1 `sameDelayApp` valM2)
    _nonMatching → False
   where
    sameDelayApp ∷ DelayApp a → DelayApp b → Bool
    sameDelayApp = curry \case
      (DelayAppUnsafeFun a, DelayAppUnsafeFun b) → a `same` b
      (DelayApp df1 da1, DelayApp df2 da2) →
        df1 `sameDelayApp` df2 && da1 `same` da2
      _nonMatching → False

{- | Lazy strategy marker.
This marker is used to identify that some action (such as merge of radix trees) must be performed in a lazy fashion.
-}
data AppDelay = AppDelay

instance (Typeable a) ⇒ Ser (Delay a) where
  ser = \case
    DelayPin a → putWord8 0 *> ser a
    DelayLazy x → runReduce (unDelayLazy (Proxy @"") x) >>= ser
    DelayCache app _memo → putWord8 1 *> ser app
  deser =
    getWord8 >>= \case
      0 → DelayPin <$> deser
      _1 → DelayCache <$> deser <*> sendAI (newIORef Nothing)

instance (Typeable a) ⇒ Ser (DelayApp a) where -- Actually, this task is mostly about serializing ust a list of [Res], which is already a thing.
-- we could use some manipulations to cut costs and reuse existing functionality.
  ser = void . ser' 0
   where
    ser' ∷ ∀ b. Word8 → DelayApp b → WriterC (RevList (Obj (Any1 Res))) SerM (EValT b)
    ser' args = \case
      DelayAppUnsafeFun f → do
        putWord8 args *> ser f
        Any1 @_ @c (Val valT _) ← fetch f
        pure $ withUnsafeEq @b @c $ EValT valT
      DelayApp f a →
        ser' (args + 1) f >>= \case
          EValT (ValTFun (ValTContainer ContainerTRes (valSerProof → Dict)) bT) → ser a $> bT
  deser = do
    args ← getWord8
    valR ← deser
    Any1 (Val valT _) ← fetch valR
    deser' args (DelayAppUnsafeFun valR) $ EValT valT
   where
    deser' ∷ ∀ a1. Word8 → DelayApp a1 → EValT a1 → ConsumeC (Obj Word64) DeserM (DelayApp a)
    deser' 0 d (evalTypeableProof → Dict) = do
      HRefl ← maybeToEmpty $ eqTypeRep (TypeRep @a1) (TypeRep @a)
      pure d
    deser' args d (EValT (ValTFun (ValTContainer ContainerTRes (valSerProof → Dict)) bT)) = do
      a ← deser
      deser' (args - 1) (DelayApp d a) bT
    deser' _args _d _nonFun = empty

builtin ∷ (Has Fresh sig m) ⇒ a → m (ResB a)
builtin v = do
  i ← fromIntegral <$> fresh
  pure
    $ assert
      (i `unsafeShiftR` (finiteBitSize i - 1) == 1)
      (ResB i v)

wrapB ∷ (Container c) ⇒ ResB a → c a
wrapB = wrap . ResBuiltin

sNothing ∷ ResB (Maybe a)
sNothing = $sFreshI $ builtin Nothing

delayAppBuiltinFun ∷ (Has Fresh sig m, InferValT a) ⇒ a → m (DelayApp a)
delayAppBuiltinFun x = DelayAppUnsafeFun . ResBuiltin <$> builtin (Any1 $ asVal x)

-- Gears definition (I don't like that it's here)

{-
Gear is a reactive cell that is a building block of Dentrado.

The core idea of Gear is simple:
> data GearIdea out = forall cache. GearIdea { initialCache ∷ !cache, run ∷ !(cache → AppIOC (out, cache)) }
I. e. a Gear is a function that has some initial "cache", and, each time it is ran, accepts
old cache as input and returns the result along with the new cache.

It is assumed that the result of Gear is actually independent of the input cache, and the cache is only
used to speed up the computation by reusing previous (cached) results.

Dentrado features slightly modernized version of Gear, that extends Gears with the concept of configuration.
Motivation: Let's suppose there is an active reactive cell that succesfully processes input data, and there
appears a need to slightly tweak its behaviour. For example, there is a running Gear that constructs the state of
the entire database, and user wants to "freeze" the current state in time, i. e. instruct Gear to stop receiving any
more events.
In naive implementation, such change of behaviour must be implemented as change of the `run` function of the Gear.
However, change of the `run` function makes it necessary to completely recomputed the entire `cache`.

To avoid this, the lifecycle of Gear is split into two parts:
1) GearTemplate — uninitialized reactive cell. It is not ready to process input.
2) Gear — a version of GearTemplate that was initialized with some context. It is ready to process input.
Both GearTemplate and Gear can be provided with updated context to produce new initialized Gear.
If a Gear was initialized from another Gear, it tries to carry the cache over instead of recalculating it from scratch.
-}

-- | A template of the Gear, which can be instantiated into GearFn.
data GearTemplate ctx (out ∷ Type) cache cfg = UnsafeGearTemplate !cache !((ctx, Maybe cfg) :-> M AppIOC cfg) !((cfg, cache) :-> M AppIOC (out, cache))
  deriving (Generic)

-- | GearFn, an instantiated GearTemplate that only needs `cache` as input.
data GearFn ctx out cache = ∀ cfg. GearFn !(ValT cfg) !cfg !(GearTemplate ctx out cache cfg)

-- | Gear, a GearFn paired with a reference to the `cache` storage.
data Gear ctx out = ∀ cache. UnsafeGear !(ValT cache) !(GearFn ctx out cache) !Int

instance (Typeable ctx, Typeable out, Ser state, Typeable cfg) ⇒ Ser (GearTemplate ctx out state cfg)
instance (Typeable ctx, Typeable out, Ser state) ⇒ Ser (GearFn ctx out state) where
  ser (GearFn cfgT@(valSerProof → Dict) cfg fn) = ser (Any1 cfgT) *> ser cfg *> ser fn
  deser = do
    Any1 cfgT@(valSerProof → Dict) ← deser
    GearFn cfgT <$> deser <*> deser
instance (Typeable ctx, Typeable out) ⇒ Ser (Gear ctx out) where
  ser (UnsafeGear cacheT@(valSerProof → Dict) fn cache) = ser (Any1 cacheT) *> ser fn *> ser cache
  deser = do
    Any1 cacheT@(valSerProof → Dict) ← deser
    UnsafeGear cacheT <$> deser <*> deser

-- An object in it's serialized form. Padded to Chunk size.
newtype Serialized a = UnsafeSerialized ByteString

-- "unstable" in a sense that serializing an object twice
-- does not necessarily yield the same result.
-- TODO: dedup, this doesn't work with dedup, at all.
unstableSerialized ∷ (Ser a) ⇒ a → AppIOC (Serialized a)
unstableSerialized x = do
  (val, UnsafeRevList refs) ← runWriter (\a b → pure (a, b)) $ runWriter (\a _ → pure a) $ ser x
  refsI ← for refs \(ObjRes (Any1 r)) → getInd r
  pure
    $ let
        unpadded = toStrictBytes $ B.toLazyByteString $ val <> mconcat (B.word64BE <$> refsI)
        padded =
          let finalSegSize = B.length unpadded `mod` 4
           in unpadded
                <> if finalSegSize == 0 -- yes, I hate myself
                  then mempty
                  else B.pack $ replicate (4 - finalSegSize) (0 ∷ Word8)
       in
        UnsafeSerialized padded

-- Right now I don't have a good idea of how this could be represented generically over both f (GearFn) and number of arguments in Haskell.
data SerializedGearFn = ∀ ctx out state. SerializedGearFn (Serialized (GearFn ctx out state))
