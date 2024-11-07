{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}

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
import Dentrado.POC.Types (Any1 (..), Dynamic1 (..), EventId, LocalEventId, RadixChunk', RadixTree, Reducible (..), Timestamp, W (..), fromEmpty, maybeToEmpty, readReducible)
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
  = ResNew !(ValT a) !a -- Ser to serialize, since serialization is a background job
  | ResUnloaded !Word64
  | ResLoaded !Word64 !a

-- | Res = ResB + ResA
data Res a
  = ResBuiltin !(ResB a)
  | ResAlloc !(MVar (ResA a))

-- Values and functions

infixr 1 :->

{- | Serializable function. Currently this is just a glorified wrapper over `ResB (a -> b)`
(i. e. a wrapper over a builtin function from `a` to `b`)
However, in future this could be greatly extended to support any lambda calculus expressions.
-}
data a :-> b where
  FunBuiltin ∷ !(ResB (a → b)) → a :-> b
  FunCurry ∷ !((a, b) :-> c) → a :-> b :-> c
  FunCurry1 {-no bang-} ∷ ValT a → !a → !((a, b) :-> c) → b :-> c

-- TODO: maybe unsafes could be cleaned by... uh... Res (c a) ~ Res (Any1 c)? well, implement Res in a way that it allows deserialized data to itself say the type.

-- | Use :-> as regular function.
funApp ∷ (InferValT True a) ⇒ a :-> b → a → b
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
-}

-- | Type of monadic computation.
data MonadT m where
  MonadTAppIOC ∷ MonadT AppIOC
  MonadTReduceC ∷ MonadT m → MonadT (ReduceC m)
  MonadTReduceC1 ∷ MonadT m → MonadT (Reduce'C "1" m)
  MonadTReduceC2 ∷ MonadT m → MonadT (Reduce'C "2" m)

-- | Boilerplate for Haskell to inference the type to store.
class (Typeable m) ⇒ InferMonadT m where
  inferMonadT ∷ MonadT m

instance InferMonadT AppIOC where
  inferMonadT = MonadTAppIOC
instance (InferMonadT m) ⇒ InferMonadT (ReduceC m) where
  inferMonadT = MonadTReduceC inferMonadT
instance (InferMonadT m) ⇒ InferMonadT (Reduce'C "1" m) where
  inferMonadT = MonadTReduceC1 inferMonadT
instance (InferMonadT m) ⇒ InferMonadT (Reduce'C "2" m) where
  inferMonadT = MonadTReduceC2 inferMonadT

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
class (Typeable a) ⇒ InferContainerT a where
  inferContainerT ∷ ContainerT a

instance InferContainerT Res where
  inferContainerT = ContainerTRes
instance InferContainerT Delay where
  inferContainerT = ContainerTDelay

-- | Extract information about stored container type from ContainerT.
containerContainerProof ∷ ContainerT a → Dict (Container a)
containerContainerProof = \case
  ContainerTRes → Dict
  ContainerTDelay → Dict

-- | No-op wrapper. Used to simplify Haskell type inference.
newtype M m a = M {unM ∷ m a}

-- | No-op wrapper. Used to simplify Haskell type inference.
newtype C c a = C {unC ∷ c a}

-- | No-op wrapper. Used to simplify Haskell type inference.
newtype B a = B {unB ∷ a}

data ValTWrapped' a b = ValTWrapped' !(EValT a → Dict (Typeable b)) !(a → b) !(b → a)

{- | ValT is a value that stores serializable type.
TODO: another cleanup?
-}
data ValT' (s ∷ Bool) a where
  ValTB ∷ !(ResB (ValT' s a)) → ValT' s (B a)
  ValTWrapped ∷ !(ResB (ValTWrapped' a b)) → !(ValT' s a) → ValT' s (W b) -- TODO: inference, nonserializable?
  ValTFun ∷ !(ValT' True a) → !(EValT b) → ValT' s (a :-> b)
  ValTUnit ∷ ValT' s ()
  ValTTuple ∷ !(ValT' s a) → !(ValT' s b) → ValT' s (a, b)
  ValTEither ∷ !(ValT' s a) → !(ValT' s b) → ValT' s (Either a b)
  ValTInt ∷ ValT' s Int
  ValTWord32 ∷ ValT' s Word32
  ValTList ∷ !(ValT' s a) → ValT' s [a]
  ValTContainer ∷ !(ContainerT c) → !(ValT' s a) → ValT' s (C c a)
  ValTRadixTree ∷ !(ContainerT c) → !(ValT' anyS k) → !(ValT' s v) → ValT' s (RadixTree c k v)
  ValTRadixChunk ∷ !(ContainerT c) → !(ValT' anyS k) → !(ValT' s v) → ValT' s (RadixChunk' c k v)
  ValTGear ∷ !(ValT' s ctx) → !(EValT out) → ValT' s (Gear ctx out)
  ValTVal ∷ ValT' s (Any1 Val)
  ValTEventId ∷ ValT' s EventId
  ValTMonad ∷ MonadT m → ValT' s a → ValT' False (M m a)
  ValTSerialized ∷ ValT' False Serialized

type ValT = ValT' True
data EValT a = ∀ anyS. EValT !(ValT' anyS a)

-- | ValT' True x is a subtype of ValT' anyS x
unser ∷ ∀ anyS a. ValT' True a → ValT' anyS a
unser x = unsafeCoerce x

{-
Note on recursive datatypes (ValTB/ValTWrapped):
It's possible that users of the library might want to implement custom recursive types.
Some new construct needs to be invented to support recursive types, and this is a problem.

The simplest approach is just to use Church encoding. It would need no modifications,
but plain Church encoding has bad asymptotics and is not efficient for many purposes. Although total.

It's *possible* to make potentially infinite types with ValT (Any1 Val), but this involves repeating
the type infinitely. Which is not that bad, but is at least 8 bytes per every indirection.

Scott encoding cannot be applied, since it needs the language to support recursive types in the
first place.

Parigot and even Stump-Fu, are bloated in my opinion (change my mind). Although total.

Stump-Mendler should be possible. And total. But, just like any other encoding, is bloated,
although

It's also possible to apply a sledgehammer, the Fix:

```idris2
data ValT = ValTTuple ValT ValT | ValTEither ValT ValT | ValTInt | ValTFix (ValT -> ValT)

mutual
  data Fix : (ValT -> ValT) -> Type where
    MkFix : hask (f (ValTFix f)) -> Fix f

  hask : ValT -> Type
  hask u = case u of
    ValTTuple a b => Pair (hask a) (hask b)
    ValTEither a b => Either (hask a) (hask b)
    ValTInt => Nat
    ValTFix f => Fix f
```
... however, I'm not sure it can be expressed without dependent types.

So the approach chosen for now is just to offload recursive types to the language:
ValTB and ValTWrapped allow additional ValT's to be expresed with Haskell.
-}

valTReducible ∷ ValT' s a → ValT' s (W (Reducible a))
valTReducible =
  ValTWrapped
    ( $sFreshI $ builtin $ ValTWrapped' (\(EValT (valTypeableProof → Dict)) → Dict) mkReducible readReducible
    )

valTMaybe ∷ ValT' s a → ValT' s (W (Maybe a))
valTMaybe =
  ValTWrapped
    ( $sFreshI
        $ builtin
        $ ValTWrapped'
          (\(EValT (ValTEither _ (valTypeableProof → Dict))) → Dict)
          (either (const Nothing) Just)
          (maybe (Left ()) Right)
    )
    . ValTEither ValTUnit

{- | Infer ValT associated with the Haskell type `a`.
"Typeable" is not required here.
-}
class (Typeable a) ⇒ InferValT s a where
  inferValT ∷ ValT' s a

instance {-# INCOHERENT #-} (InferValT True a, Typeable a) ⇒ InferValT False a where
  inferValT = unsafeCoerce @(ValT' True a) @(ValT' False a) $ inferValT @True @a
instance (InferValT True a, InferValT False b) ⇒ InferValT True (a :-> b) where
  inferValT = ValTFun inferValT (EValT $ inferValT @False)
instance (InferValT s a, InferValT s b) ⇒ InferValT s (a, b) where
  inferValT = ValTTuple inferValT inferValT
instance (InferValT s a, InferValT s b) ⇒ InferValT s (Either a b) where
  inferValT = ValTEither inferValT inferValT
instance InferValT s () where
  inferValT = ValTUnit
instance InferValT s Int where
  inferValT = ValTInt
instance (InferValT s ctx, InferValT False out) ⇒ InferValT s (Gear ctx out) where
  inferValT = ValTGear inferValT (EValT $ inferValT @False)
instance InferValT s Word32 where
  inferValT = ValTWord32
instance (InferContainerT c, InferValT s v) ⇒ InferValT s (C c v) where
  inferValT = ValTContainer inferContainerT inferValT
instance (InferContainerT c, InferValT False k, InferValT s v) ⇒ InferValT s (RadixTree c k v) where
  inferValT = ValTRadixTree inferContainerT (inferValT @False) inferValT
instance (InferContainerT c, InferValT False k, InferValT s v) ⇒ InferValT s (RadixChunk' c k v) where
  inferValT = ValTRadixChunk inferContainerT (inferValT @False) inferValT
instance (InferValT s a) ⇒ InferValT s [a] where
  inferValT = ValTList inferValT
instance InferValT s (Any1 Val) where
  inferValT = ValTVal
instance InferValT s EventId where
  inferValT = ValTEventId
instance (InferMonadT m, InferValT False a) ⇒ InferValT False (M m a) where
  inferValT = ValTMonad inferMonadT (inferValT @False)
instance InferValT False Serialized where
  inferValT = ValTSerialized

instance (InferValT s a) ⇒ InferValT s (W (Reducible a)) where
  inferValT = valTReducible inferValT
instance (InferValT s a) ⇒ InferValT s (W (Maybe a)) where
  inferValT = valTMaybe inferValT

-- | Val a = ValT + a
data Val a = Val !(ValT' True a) !a

data EVal a = EVal !(EValT a) !a

-- | Convert Haskell value of type `a` into `Val a`.
asVal ∷ (InferValT True a) ⇒ a → Val a
asVal = Val inferValT

-- Env

-- | Computation provided by the external system to load elements from the disk.
newtype EnvLoad = EnvLoad (∀ a. ValT a → Word64 → IO a)

-- | Computation provided by the external system to store elements to the disk.
newtype EnvStore = EnvStore (∀ a. ValT a → a → IO Word64)

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
  , envGearsIndex ∷ !(MVar (RadixTree Res Serialized Int)) -- index of initialized Gears (reactive cells).
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

-- Resource utils

-- | Perform "allocation", turning `a` into `Res a`.
alloc ∷ (Has AppIO sig m, InferValT True a) ⇒ a → m (Res a)
alloc v = ResAlloc <$> sendAI (newMVar $ ResNew inferValT v)
{-# INLINE alloc #-}

{- | Perform fetch by loading the value `a` from `Res a`.
This operation potentially causes disk access! (envLoad)
-}
fetch ∷ ∀ sig m a. (Has AppIO sig m, InferValT True a) ⇒ Res a → m a
fetch = \case
  ResBuiltin (ResB _ v) → pure v
  ResAlloc ref → do
    EnvLoad load ← asks envLoad
    sendAI $ tryLazy ref $ pure . \case
      ResNew _ v → Left v
      ResLoaded _ v → Left v
      ResUnloaded k → Right do
        v ← liftIO $ load inferValT k
        pure (ResLoaded k v, v)
{-# INLINE fetch #-}

-- | Attempt to fetch the value without accessing the disk.
tryFetch ∷ Res a → Maybe a
tryFetch = \case
  ResBuiltin (ResB _ v) → Just v
  ResAlloc ref → case unsafePerformIO $ readMVar ref of
    ResNew _ v → Just v
    ResUnloaded _ → Nothing
    ResLoaded _ v → Just v

builtin ∷ (Has Fresh sig m) ⇒ a → m (ResB a)
builtin v = do
  i ← fromIntegral <$> fresh
  pure
    $ assert
      (i `unsafeShiftR` (finiteBitSize i - 1) == 1)
      (ResB i v)

wrapB ∷ (Container c) ⇒ ResB a → c a
wrapB = wrap . ResBuiltin

valTypeableProof ∷ ValT' s x → Dict (Typeable x)
valTypeableProof = \case
  ValTB (ResB _ (valTypeableProof → Dict)) → Dict
  ValTWrapped (ResB _ u) aT → u & (\(ValTWrapped' f _ _) → f $ EValT aT) & \Dict → Dict
  ValTFun (valTypeableProof → Dict) (EValT (valTypeableProof → Dict)) → Dict
  ValTUnit → Dict
  ValTTuple (valTypeableProof → Dict) (valTypeableProof → Dict) → Dict
  ValTEither (valTypeableProof → Dict) (valTypeableProof → Dict) → Dict
  ValTInt → Dict
  ValTWord32 → Dict
  ValTList (valTypeableProof → Dict) → Dict
  ValTContainer (containerContainerProof → Dict) (valTypeableProof → Dict) → Dict
  ValTRadixTree (containerContainerProof → Dict) (valTypeableProof → Dict) (valTypeableProof → Dict) → Dict
  ValTRadixChunk (containerContainerProof → Dict) (valTypeableProof → Dict) (valTypeableProof → Dict) → Dict
  ValTGear (valTypeableProof → Dict) (EValT (valTypeableProof → Dict)) → Dict
  ValTVal → Dict
  ValTEventId → Dict
  ValTMonad (monadTypeableProof → Dict) (valTypeableProof → Dict) → Dict
  ValTSerialized → Dict

-- Reduce

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

-- instance (Ser a) ⇒ Ser (Reducible a) where
--   ser = ser . readReducible
--   deser = mkReducible <$> deser

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

-- | Attempt to extract a value of type `a` from `Val` over statically unknown type.
tryFromVal ∷ ∀ a. (Typeable a) ⇒ Any1 Val → Maybe a
tryFromVal (Any1 (Val @b (valTypeableProof → Dict) a)) =
  (\HRefl → a) <$> eqTypeRep (TypeRep @a) (TypeRep @b)

-- Val conversion

-- Container (Res/Delay)

-- | Interface for Res/Delay. This is used to make it possible to write code generic over the actual used container.
class (Typeable t, InferContainerT t) ⇒ Container t where
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
allocC ∷ (Container t, Has AppIO sig m, InferValT True a) ⇒ a → m (t a)
allocC x = wrap <$> alloc x
{-# INLINE allocC #-}

-- | Generalized `unwrap`.
unwrap ∷ (Container c, Has (AppIO :+: Reduce) sig m) ⇒ c a → m (Res a)
unwrap = unwrap' $ Proxy @""

-- | Generalized `tryFetch`.
tryFetchC ∷ (Container c) ⇒ c a → Maybe a
tryFetchC c = tryUnwrap c >>= tryFetch

-- | Generalized fetch.
fetchC' ∷ (Container c, Has (AppIO :+: Reduce' s) sig m, InferValT True a) ⇒ Proxy s → c a → m a
fetchC' proxy x = fetch =<< unwrap' proxy x
{-# INLINE fetchC' #-}

-- | Generalized fetch.
fetchC ∷ (Container c, Has (AppIO :+: Reduce) sig m, InferValT True a) ⇒ c a → m a
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
    -- \$ EVal (EValT vT) v
    DelayApp (f ∷ DelayApp (C Res a :-> y)) a →
      delayAppVal' f >>= \case
        EVal (EValT (ValTFun aT@(valTypeableProof → Dict) bT)) f' →
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

sNothing ∷ ResB (W (Maybe a))
sNothing = $sFreshI $ builtin $ W Nothing

delayAppBuiltinFun ∷ (Has Fresh sig m, InferValT True a) ⇒ a → m (DelayApp a)
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
data GearTemplate ctx (out ∷ Type) cache cfg = UnsafeGearTemplate !cache !((ctx, W (Maybe cfg)) :-> M AppIOC cfg) !((cfg, cache) :-> M AppIOC (out, cache))
  deriving (Generic)

-- | GearFn, an instantiated GearTemplate that only needs `cache` as input.
data GearFn ctx out cache = ∀ cfg. GearFn !(ValT cfg) !cfg !(GearTemplate ctx out cache cfg)

-- | Gear, a GearFn paired with a reference to the `cache` storage.
data Gear ctx out = ∀ cache. UnsafeGear !(ValT cache) !(GearFn ctx out cache) !Int

newtype Serialized = UnsafeSerialized ByteString

class GStruct (f ∷ k → Type) where
  type GStructValT f ∷ Type

  gStruct ∷ f x → GStructValT f
  gUnstruct ∷ GStructValT f → f x

instance (GStruct a, GStruct b) ⇒ GStruct (a G.:+: b) where
  type GStructValT (a G.:+: b) = Either (GStructValT a) (GStructValT b)
  gStruct = \case
    G.L1 a → Left $ gStruct a
    G.R1 b → Right $ gStruct b
  gUnstruct = \case
    Left a → G.L1 $ gUnstruct a
    Right b → G.R1 $ gUnstruct b

instance (GStruct a, GStruct b) ⇒ GStruct (a G.:*: b) where
  type GStructValT (a G.:*: b) = (GStructValT a, GStructValT b)
  gStruct (a G.:*: b) = (gStruct a, gStruct b)
  gUnstruct (a, b) = gUnstruct a G.:*: gUnstruct b

instance (GStruct a) ⇒ GStruct (G.M1 i c a) where
  type GStructValT (G.M1 i c a) = GStructValT a
  gStruct (G.M1 x) = gStruct x
  gUnstruct = G.M1 . gUnstruct

instance GStruct (G.K1 i a) where
  type GStructValT (G.K1 i a) = a
  gStruct (G.K1 a) = a
  gUnstruct = G.K1

instance GStruct G.U1 where
  type GStructValT G.U1 = ()
  gStruct G.U1 = ()
  gUnstruct _ = G.U1

struct ∷ (Generic a, GStruct (G.Rep a)) ⇒ a → GStructValT (G.Rep a)
struct = gStruct . G.from

unstruct ∷ (Generic a, GStruct (G.Rep a)) ⇒ GStructValT (G.Rep a) → a
unstruct = G.to . gUnstruct
