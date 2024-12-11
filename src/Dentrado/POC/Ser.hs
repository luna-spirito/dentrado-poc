module Dentrado.POC.Ser where

import Control.Algebra
import Control.Carrier.Empty.Church (EmptyC)
import Control.Carrier.State.Church (StateC, get, put)
import Control.Carrier.Writer.Church (WriterC, runWriter)
import Control.Effect.Empty (Empty)
import qualified Control.Effect.Empty as E
import Control.Effect.Reader (asks)
import Control.Effect.Sum
import Data.Bits (Bits (unsafeShiftL), finiteBitSize, unsafeShiftR, (.|.))
import qualified Data.ByteString.Builder as B
import qualified Data.ByteString.Unsafe as B
import Data.Constraint (Dict (..))
import Data.Dynamic (Dynamic (..), fromDynamic)
import Data.Functor.Compose (Compose (..))
import qualified Data.IntMap as IMap
import Data.Kind (Type)
import Data.Tuple (swap)
import Dentrado.POC.Memory (AppIOC, C (..), ContainerT (..), Delay (..), DelayApp (..), EValT (..), Env (..), EnvStore (..), Gear (..), GearFn (..), GearTemplate (..), MonadT (..), PaddedByteString (..), Res (..), Res' (..), ResA (..), ResACell (..), ResB (..), RevList (..), Serialized (..), Val (..), ValT, ValT' (..), ValTWrapped' (..), ValTWrapped1' (..), eqValT, fetch, runReduce, sendAI, tryLazy, unDelayLazy, unser, valTMaybe, valTReducible, valTypeableProof, withUnsafeEq, (:->) (..))
import Dentrado.POC.TH (moduleId)
import Dentrado.POC.Types (Any1 (..), Dynamic1 (..), EventId (..), LocalEventId (..), RadixChunk' (..), RadixTree (..), Timestamp (..), W (..), W1 (..), maybeToEmpty)
import RIO hiding (asks)
import qualified RIO.ByteString as B
import RIO.List (uncons)
import qualified RIO.List as L
import qualified RIO.Partial as P
import System.Mem.Weak (deRefWeak, mkWeakPtr)
import qualified Type.Reflection as T
import Unsafe.Coerce (unsafeCoerce)
import Control.Effect.Writer

$(moduleId 4)

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

type SerM' = WriterC (RevList (Obj (Any1 Res'))) SerM
type DeserM' = ConsumeC (Obj Word64) DeserM

serWord8 ∷ Has (Writer Builder) sig m => Word8 → m ()
serWord8 = tell . B.word8
{-# INLINE serWord8 #-}

getWord8 ∷ DeserM' Word8
getWord8 = do
  old ← get
  (x, new) ← maybeToEmpty $ B.uncons old
  put new
  pure x

-- ValT serialization

serMonadT ∷ MonadT m → SerM' ()
serMonadT = \case
  MonadTAppIOC → serWord8 0
  MonadTReduceC y → serWord8 1 *> serMonadT y
  MonadTReduceC1 y → serWord8 2 *> serMonadT y
  MonadTReduceC2 y → serWord8 3 *> serMonadT y

deserMonadT ∷ DeserM' (Any1 MonadT)
deserMonadT =
  getWord8 >>= \case
    0 → pure $ Any1 MonadTAppIOC
    1 → do
      Any1 x ← deserMonadT
      pure $ Any1 $ MonadTReduceC x
    2 → do
      Any1 x ← deserMonadT
      pure $ Any1 $ MonadTReduceC1 x
    _3 → do
      Any1 x ← deserMonadT
      pure $ Any1 $ MonadTReduceC2 x

serContainerT ∷ ContainerT a → SerM' ()
serContainerT = \case
  ContainerTRes → serWord8 0
  ContainerTDelay → serWord8 1

deserContainerT ∷ DeserM' (Any1 ContainerT)
deserContainerT =
  getWord8 <&> \case
    0 → Any1 ContainerTRes
    _1 → Any1 ContainerTDelay

serValT ∷ ValT' s a → SerM' ()
serValT = \case
  ValTFun a (EValT b) → serWord8 0 *> serValT a *> serValT b
  ValTUnit → serWord8 1
  ValTTuple a b → serWord8 2 *> serValT a *> serValT b
  ValTEither a b → serWord8 3 *> serValT a *> serValT b
  ValTInt → serWord8 4
  ValTWord32 → serWord8 5
  ValTList a → serWord8 6 *> serValT a
  ValTContainer c v → serWord8 7 *> serContainerT c *> serValT v
  ValTRadixTree c k v → serWord8 8 *> serContainerT c *> serValT k *> serValT v
  ValTRadixChunk c k v → serWord8 9 *> serContainerT c *> serValT k *> serValT v
  ValTGear ctx (EValT out) → serWord8 10 *> serValT ctx *> serValT out
  ValTVal → serWord8 11
  -- ValTB x → serWord8 12 *> serResB x
  ValTWrapped x → serWord8 12 *> serResB x
  ValTWrapped1 x a → serWord8 13 *> serResB x *> serValT a
  ValTEventId → serWord8 14
  ValTByteString → serWord8 15
  ValTMonad mT vT → serWord8 150 *> serMonadT mT *> serValT vT
  ValTSerialized → serWord8 151

-- >= 150 RESERVED FOR EVAL

deserValT ∷ DeserM' (Any1 ValT)
deserValT =
  getWord8 >>= \case
    0 → do
      Any1 a ← deserValT
      Any1 b ← deserEValT
      pure $ Any1 $ ValTFun a b
    1 → pure $ Any1 ValTUnit
    2 → do
      Any1 a ← deserValT
      Any1 b ← deserValT
      pure $ Any1 $ ValTTuple a b
    3 → do
      Any1 a ← deserValT
      Any1 b ← deserValT
      pure $ Any1 $ ValTEither a b
    4 → pure $ Any1 ValTInt
    5 → pure $ Any1 ValTWord32
    6 → do
      Any1 a ← deserValT
      pure $ Any1 $ ValTList a
    7 → do
      Any1 c ← deserContainerT
      Any1 v ← deserValT
      pure $ Any1 $ ValTContainer c v
    8 → do
      Any1 c ← deserContainerT
      Any1 (EValT k) ← deserEValT
      Any1 v ← deserValT
      pure $ Any1 $ ValTRadixTree c k v
    9 → do
      Any1 c ← deserContainerT
      Any1 k ← deserValT
      Any1 v ← deserValT
      pure $ Any1 $ ValTRadixChunk c k v
    10 → do
      Any1 ctx ← deserValT
      Any1 out ← deserEValT
      pure $ Any1 $ ValTGear ctx out
    11 → pure $ Any1 ValTVal
    12 → do
      Dynamic1 rep res ← deserResB'
      case rep of
        valTWrapped' `T.App` s `T.App` _over
          | Just T.HRefl ← T.eqTypeRep valTWrapped' (T.TypeRep @ValTWrapped')
          , Just T.HRefl ← T.eqTypeRep s (T.TypeRep @True) →
              pure $ Any1 $ ValTWrapped res
        _ → E.empty
    13 → do
      Dynamic1 rep res ← deserResB'
      Any1 a ← deserValT
      case rep of
        valTWrapped1' `T.App` _f
          | Just T.HRefl ← T.eqTypeRep valTWrapped1' (T.TypeRep @ValTWrapped1') →
              pure $ Any1 $ ValTWrapped1 res a
        _ → E.empty
    14 → E.empty
    150 → E.empty -- ValTMonad
    _151 → E.empty -- ValTSerialized

withEquatedSer ∷ ∀ s1 a s2 b c. (ValT' s1 a → ValT' s1 b → c) → ValT' s1 a → ValT' s2 b → c
withEquatedSer f a b = f a (unsafeCoerce @(ValT' s2 b) @(ValT' s1 b) b)

-- TODO: Deduplicate
deserEValT ∷ DeserM' (Any1 EValT)
deserEValT =
  getWord8 >>= \case
    0 → do
      Any1 a ← deserValT
      Any1 b ← deserEValT
      pure $ Any1 $ EValT $ ValTFun a b
    1 → pure $ Any1 $ EValT ValTUnit
    2 → do
      Any1 (EValT a) ← deserEValT
      Any1 (EValT b) ← deserEValT
      pure $ Any1 $ EValT $ withEquatedSer ValTTuple a b
    3 → do
      Any1 (EValT a) ← deserEValT
      Any1 (EValT b) ← deserEValT
      pure $ Any1 $ EValT $ withEquatedSer ValTEither a b
    4 → pure $ Any1 $ EValT ValTInt
    5 → pure $ Any1 $ EValT ValTWord32
    6 → do
      Any1 (EValT a) ← deserEValT
      pure $ Any1 $ EValT $ ValTList a
    7 → do
      Any1 c ← deserContainerT
      Any1 (EValT v) ← deserEValT
      pure $ Any1 $ EValT $ ValTContainer c v
    8 → do
      Any1 c ← deserContainerT
      Any1 (EValT k) ← deserEValT
      Any1 (EValT v) ← deserEValT
      pure $ Any1 $ EValT $ withEquatedSer (ValTRadixTree c) k v
    9 → do
      Any1 c ← deserContainerT
      Any1 (EValT k) ← deserEValT
      Any1 (EValT v) ← deserEValT
      pure $ Any1 $ EValT $ withEquatedSer (ValTRadixChunk c) k v
    10 → do
      Any1 (EValT ctx) ← deserEValT
      Any1 out ← deserEValT
      pure $ Any1 $ EValT $ ValTGear ctx out
    11 → pure $ Any1 $ EValT ValTVal
    12 → do
      Dynamic1 rep res ← deserResB'
      case rep of
        valTWrapped' `T.App` _s `T.App` _over
          | Just T.HRefl ← T.eqTypeRep valTWrapped' (T.TypeRep @ValTWrapped') →
              pure $ Any1 $ EValT $ ValTWrapped res
        _ → E.empty
    13 → do
      Dynamic1 rep res ← deserResB'
      Any1 (EValT a) ← deserEValT
      case rep of
        valTWrapped1' `T.App` _f
          | Just T.HRefl ← T.eqTypeRep valTWrapped1' (T.TypeRep @ValTWrapped1') →
              pure $ Any1 $ EValT $ ValTWrapped1 res a
        _ → E.empty
    14 → pure $ Any1 $ EValT ValTEventId
    150 → do
      Any1 mT ← deserMonadT
      Any1 vT ← deserValT
      pure $ Any1 $ EValT $ ValTMonad mT vT
    _151 → pure $ Any1 $ EValT ValTSerialized

serVal ∷ Val a → SerM' ()
serVal (Val xT x) = serValT xT *> ser xT x

deserVal ∷ DeserM' (Any1 Val)
deserVal = do
  Any1 xT ← deserValT
  Any1 . Val xT <$> deser xT

-- Val serialization

{- | Serialization of ResB is performed just by instructing the system to store the pointer.
Pointer serialization is queued and is not performed instantly, since that would require to
force serialization of the referenced object.
-}
serResB ∷ ResB a → SerM' ()
serResB = serRes' . ResBuiltin

deserResB' ∷ DeserM' (Dynamic1 ResB)
deserResB' = do
  addr ∷ Word64 ←
    consume >>= \case
      ObjRes addr → pure addr
      _notRes → E.empty
  builtins ← asks envBuiltins
  Dynamic rep val ← maybeToEmpty $ IMap.lookup (fromIntegral addr) builtins
  pure $ Dynamic1 rep $ ResB addr val

deserResB ∷ ∀ a. (Typeable a) ⇒ DeserM' (ResB a)
deserResB = do
  Dynamic1 rep res ← deserResB'
  T.HRefl ← maybeToEmpty $ T.eqTypeRep rep (T.TypeRep @a)
  pure res

serRes' ∷ Res' a → SerM' ()
serRes' x = tell @(RevList (Obj (Any1 Res'))) [ObjRes $ Any1 x]

serRes ∷ ValT a → Res a → SerM' ()
serRes aT = \case
  ResI a → ser aT a
  ResNoI a → serRes' a

deserRes ∷ ∀ a. ValT a → DeserM' (Res a)
deserRes aT = do
  addr ∷ Word64 ←
    consume >>= \case
      ObjRes addr → pure addr
      _notRes → E.empty
  getWord8 >>= \case
    0 → ResI <$> deser aT
    _1 →
      ResNoI
        <$> if (addr `unsafeShiftR` (finiteBitSize addr - 1)) == 1
          then
            ResBuiltin <$> do
              builtins ← asks envBuiltins
              Dict ← pure $ valTypeableProof aT
              pure $ ResB addr $ P.fromJust $ fromDynamic $ P.fromJust $ IMap.lookup (fromIntegral addr) builtins -- TODO-post-POC
          else
            ResAlloc <$> do
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
                                -- new ← ResAlloc <$> newMVar (ResUnloaded addr)
                                new ← newMVar $ ResUnloaded addr
                                (new,) . Just <$> mkWeakPtr (ResACell aT new) (Just cleanupAddr)
                              Just (ResACell eT existing) →
                                (,existingWeak) <$> do
                                  Just Dict ← pure $ eqValT aT eT
                                  pure existing
                        )
                        (fromIntegral addr)
                        oldKnown
                    )

serWord32 ∷ Has (Writer Builder) sig m => Word32 → m ()
serWord32 = tell . B.word32BE
{-# INLINE serWord32 #-}

-- TODO: unsafeTake/unsafeDrop?

deserWord32 ∷ DeserM' Word32
deserWord32 = do
  old ← get
  E.guard (B.length old >= 4)
  put $ B.drop 4 old
  -- https://hackage.haskell.org/package/cereal-0.5.8.3/docs/src/Data.Serialize.Get.html#getWord32be
  pure
    $ (fromIntegral @_ @Word32 (old `B.unsafeIndex` 0) `unsafeShiftL` 24)
    .|. (fromIntegral @_ @Word32 (old `B.unsafeIndex` 1) `unsafeShiftL` 16)
    .|. (fromIntegral @_ @Word32 (old `B.unsafeIndex` 2) `unsafeShiftL` 8)
    .|. fromIntegral @_ @Word32 (old `B.unsafeIndex` 3)

serWord64 ∷ Has (Writer Builder) sig m => Word64 → m ()
serWord64 = tell . B.word64BE
{-# INLINE serWord64 #-}

deserWord64 ∷ DeserM' Word64
deserWord64 = do
  old ← get
  E.guard (B.length old >= 8)
  put $ B.drop 8 old
  pure $! (fromIntegral (old `B.unsafeIndex` 0) `unsafeShiftL` 56)
    .|. (fromIntegral (old `B.unsafeIndex` 1) `unsafeShiftL` 48)
    .|. (fromIntegral (old `B.unsafeIndex` 2) `unsafeShiftL` 40)
    .|. (fromIntegral (old `B.unsafeIndex` 3) `unsafeShiftL` 32)
    .|. (fromIntegral (old `B.unsafeIndex` 4) `unsafeShiftL` 24)
    .|. (fromIntegral (old `B.unsafeIndex` 5) `unsafeShiftL` 16)
    .|. (fromIntegral (old `B.unsafeIndex` 6) `unsafeShiftL` 8)
    .|. (fromIntegral (old `B.unsafeIndex` 7))

-- TODO: Varint
serInt ∷ Has (Writer Builder) sig m => Int → m ()
serInt = serWord64 . fromIntegral

deserInt ∷ DeserM' Int
deserInt = fromIntegral <$> deserWord64

serByteString ∷ ByteString → SerM' ()
serByteString x = serInt (B.length x) *> tell (B.byteString x)

deserByteString ∷ DeserM' ByteString
deserByteString = do
  len ← deserInt
  old ← get
  E.guard (B.length old >= len)
  put $ B.drop len old
  pure $ B.copy $ B.take len old

serFn ∷ ∀ a b. a :-> b → SerM' ()
serFn = \case
  FunBuiltin x → serWord8 0 *> serResB x
  FunCurry f → serWord8 1 *> serFn f
  FunCurry1 xT x f → serWord8 2 *> serVal (Val xT x) *> serFn f

deserFn ∷ ∀ a b. ValT a → EValT b → DeserM' (a :-> b)
deserFn aT (EValT bT) =
  getWord8 >>= \case
    0
      | Dict ← valTypeableProof aT
      , Dict ← valTypeableProof bT →
          FunBuiltin <$> deserResB
    1 → case bT of
      (ValTFun cT eT) → FunCurry <$> deserFn (ValTTuple aT cT) eT
      _nonFun → E.empty
    _2 → do
      Any1 (Val xT x) ← deserVal
      FunCurry1 xT x <$> deserFn (ValTTuple xT aT) (EValT bT)

serDelay ∷ ValT a → Delay a → SerM' ()
serDelay aT = \case
  DelayPin a → serWord8 0 *> serRes aT a
  DelayLazy x → runReduce (unDelayLazy (Proxy @"") x) >>= serDelay aT
  DelayCache app _memo → serWord8 1 *> serDelayApp app

deserDelay ∷ ValT a → DeserM' (Delay a)
deserDelay aT =
  getWord8 >>= \case
    0 → DelayPin <$> deserRes aT
    _1 → DelayCache <$> deserDelayApp (ValTMonad MonadTAppIOC $ ValTContainer ContainerTRes aT) <*> sendAI (newIORef Nothing)

serDelayApp ∷ DelayApp a → SerM' ()
serDelayApp = void . ser' 0
 where
  ser' ∷ ∀ b. Word8 → DelayApp b → SerM' (EValT b)
  ser' args = \case
    DelayAppUnsafeFun f → do
      serWord8 args *> serRes ValTVal f
      Any1 @_ @c (Val valT _) ← fetch f
      pure $ withUnsafeEq @b @c $ EValT valT
    DelayApp f a →
      ser' (args + 1) f >>= \case
        EValT (ValTFun (ValTContainer ContainerTRes aT) bT) →
          serDelay aT a $> bT

deserDelayApp ∷ ∀ s a. ValT' s a → DeserM' (DelayApp a)
deserDelayApp resT = do
  args ← getWord8
  valR ← deserRes ValTVal
  Any1 (Val valT _) ← fetch valR
  deser' args (DelayAppUnsafeFun valR) $ EValT valT
 where
  deser' ∷ ∀ a1. Word8 → DelayApp a1 → EValT a1 → ConsumeC (Obj Word64) DeserM (DelayApp a)
  deser' 0 d (EValT dT) = do
    Dict ← maybeToEmpty $ eqValT resT dT
    pure d
  deser' args d (EValT (ValTFun (ValTContainer ContainerTRes aT) bT)) = do
    a ← deserDelay aT
    deser' (args - 1) (DelayApp d a) bT
  deser' _args _d _nonFun = E.empty

serContainer ∷ ContainerT c → ValT a → c a → SerM' ()
serContainer c = case c of
  ContainerTRes → serRes
  ContainerTDelay → serDelay

deserContainer ∷ ContainerT c → ValT a1 → ConsumeC (Obj Word64) DeserM (c a1)
deserContainer c aT = case c of
  ContainerTRes → deserRes aT
  ContainerTDelay → deserDelay aT

serRT ∷ ContainerT c → ValT' anyS k → ValT v → RadixTree c k v → SerM' ()
serRT cT kT vT (RadixTree val chunk) = serContainer cT (valTMaybe vT) val *> serContainer cT (valTReducible $ ValTRadixChunk cT kT vT) chunk

deserRT ∷ ContainerT c → ValT' s k → ValT a → DeserM' (RadixTree c k a)
deserRT cT kT vT = RadixTree <$> deserContainer cT (valTMaybe vT) <*> deserContainer cT (valTReducible $ ValTRadixChunk cT kT vT)

serRC ∷ ContainerT c → ValT' s k → ValT v → RadixChunk' c k v → SerM' ()
serRC cT kT vT = \case
  Nil → serWord8 0
  Tip chunk rt → serWord8 1 *> serWord32 chunk *> serRT cT kT vT rt
  Bin chunk sub1 sub2 →
    serWord8 2
      *> serWord32 chunk
      *> serContainer cT (valTReducible $ ValTRadixChunk cT kT vT) sub1
      *> serContainer cT (valTReducible $ ValTRadixChunk cT kT vT) sub2

deserRC ∷ ContainerT c → ValT' s k → ValT v → DeserM' (RadixChunk' c k v)
deserRC cT kT vT =
  getWord8 >>= \case
    0 → pure Nil
    1 → Tip <$> deserWord32 <*> deserRT cT kT vT
    _2 → Bin <$> deserWord32 <*> deserContainer cT (valTReducible $ ValTRadixChunk cT kT vT) <*> deserContainer cT (valTReducible $ ValTRadixChunk cT kT vT)

serGearTemplate ∷ ValT cache → GearTemplate ctx out cache cfg → SerM' ()
serGearTemplate cacheT (UnsafeGearTemplate cache cfg fn) = ser cacheT cache *> serFn cfg *> serFn fn

deserGearTemplate ∷ ValT ctx → EValT out → ValT cache → ValT cfg → DeserM' (GearTemplate ctx out cache cfg)
deserGearTemplate ctxT (EValT outT) cacheT cfgT =
  UnsafeGearTemplate
    <$> deser cacheT
    <*> deserFn (ValTTuple ctxT $ valTMaybe cfgT) (EValT $ ValTMonad MonadTAppIOC cfgT)
    <*> deserFn (ValTTuple cfgT cacheT) (EValT $ ValTMonad MonadTAppIOC $ ValTTuple outT $ unser cacheT)

serGearFn ∷ ValT cache → GearFn ctx out cache → SerM' ()
serGearFn cacheT (GearFn cfgT cfg fn) = serValT cfgT *> ser cfgT cfg *> serGearTemplate cacheT fn

deserGearFn ∷ ValT ctx → EValT out → ValT cache → DeserM' (GearFn ctx out cache)
deserGearFn ctxT outT cacheT = do
  Any1 cfgT ← deserValT
  GearFn cfgT <$> deser cfgT <*> deserGearTemplate ctxT outT cacheT cfgT

serGear ∷ Gear ctx out → SerM' ()
serGear (UnsafeGear cacheT fn cache) = serValT cacheT *> serGearFn cacheT fn *> serInt cache

deserGear ∷ ValT ctx → EValT out → DeserM' (Gear ctx out)
deserGear ctxT outT = do
  Any1 cacheT ← deserValT
  UnsafeGear cacheT <$> deserGearFn ctxT outT cacheT <*> deserInt

ser ∷ ValT a → a → SerM' ()
ser = \case
  -- ValTB (ResB _ aT) → ser aT . unB
  -- ValTWrapped (ResB _ (ValTWrapped' {-_-} _ g)) aT → ser aT . g . unW
  ValTWrapped (ResB _ (ValTWrapped' _ uT un _)) → ser uT . un . unW
  ValTWrapped1 (ResB _ (ValTWrapped1' _ f)) oT →
    case f oT of
      ValTWrapped' _ uT un _ → ser uT . un . unW1
  ValTFun _a _b → serFn
  ValTUnit → pure
  ValTTuple a b → \(a', b') → ser a a' *> ser b b'
  ValTEither a b → \case
    Left a' → serWord8 0 *> ser a a'
    Right b' → serWord8 1 *> ser b b'
  ValTInt → serInt
  ValTWord32 → serWord32
  ValTList a → \l → serInt (L.length l) *> for_ l (ser a)
  ValTContainer c a → serContainer c a . unC
  ValTRadixTree cT kT vT → serRT cT kT vT
  ValTRadixChunk cT kT vT → serRC cT kT vT
  ValTGear _ _ → serGear
  ValTVal → \(Any1 v) → serVal v
  ValTEventId → \(EventId (Timestamp a) (LocalEventId b)) → serWord32 a *> serWord32 b
  ValTByteString → serByteString

deser ∷ ValT a → DeserM' a
deser = \case
  -- ValTB (ResB _ aT) → B <$> deser aT
  ValTWrapped (ResB _ (ValTWrapped' _ aT _ mk)) → W . mk <$> deser aT
  ValTWrapped1 (ResB _ (ValTWrapped1' _ f)) oT →
    case f oT of
      ValTWrapped' _ uT _ mk → W1 . mk <$> deser uT
  ValTFun aT bT → deserFn aT bT
  ValTUnit → pure ()
  ValTTuple a b → (,) <$> deser a <*> deser b
  ValTEither a b →
    getWord8 >>= \case
      0 → Left <$> deser a
      _1 → Right <$> deser b
  ValTInt → deserInt
  ValTWord32 → deserWord32
  ValTList a → deserInt >>= \l → sequenceA $ replicate l (deser a)
  ValTContainer c a → C <$> deserContainer c a
  ValTRadixTree cT kT vT → deserRT cT kT vT
  ValTRadixChunk cT kT vT → deserRC cT kT vT
  ValTGear ctxT outT → deserGear ctxT outT
  ValTVal → deserVal
  ValTEventId → EventId <$> (Timestamp <$> deserWord32) <*> (LocalEventId <$> deserWord32)
  ValTByteString → deserByteString

{- | Force serialization of the object and acquire its identifier.
TODO: Remove if possible.
-}
getInd ∷ ∀ a. Res' a → AppIOC Word64
getInd = \case
  ResBuiltin (ResB i _) → pure i
  ResAlloc xV → do
    EnvStore store ← asks envStore
    sendAI $ tryLazy xV $ pure . \case
      ResUnloaded i → Left i
      ResLoaded i _ → Left i
      ResNew v@(Val _ v') → Right do
        i ← liftIO $ store v
        pure (ResLoaded i v', i)

pad ∷ ByteString → PaddedByteString
pad unpadded =
  UnsafePaddedByteString
    $ let finalSegSize = B.length unpadded `mod` 4
       in unpadded
            <> if finalSegSize == 0 -- yes, I hate myself
              then mempty
              else B.pack $ replicate (4 - finalSegSize) (0 ∷ Word8)

unpad ∷ PaddedByteString → ByteString
unpad (UnsafePaddedByteString x) = B.dropWhileEnd (== 0) x

-- "unstable" in a sense that serializing an object twice
-- does not necessarily yield the same result.
-- TODO: dedup, this doesn't work with dedup, at all.
unstableSerialized ∷ SerM' () → AppIOC Serialized
unstableSerialized act = do
  (val, UnsafeRevList refs) ← runWriter (\a b → pure (a, b)) $ runWriter (\a _ → pure a) act
  refsI ← for refs \(ObjRes (Any1 r)) → getInd r
  pure
    $ let unpadded = toStrictBytes $ B.toLazyByteString $ val <> mconcat (B.word64BE <$> refsI)
       in UnsafeSerialized $ pad unpadded
