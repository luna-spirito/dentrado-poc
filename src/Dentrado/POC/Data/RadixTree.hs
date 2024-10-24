{-# LANGUAGE RecursiveDo, PatternSynonyms #-}
{-# LANGUAGE ConstraintKinds #-}
module Dentrado.POC.Data.RadixTree where
import RIO hiding (lookup, Set, Map, mask, toList, catch, runReader, (<|>))
import Data.Bits (countTrailingZeros, (.&.), unsafeShiftR, complement, xor, finiteBitSize, unsafeShiftL, (.|.), countLeadingZeros)
import Control.Algebra
import Data.Foldable (foldrM)
import Dentrado.POC.TH (moduleId, sFreshI)
import Control.Carrier.Writer.Church (WriterC, runWriter)
import Control.Monad.Fix (MonadFix)
import Data.Monoid (First(..))
import Control.Effect.NonDet (NonDet)
import Control.Effect.Choose (Choose(..), (<|>))
import qualified Control.Effect.Empty as E
import GHC.Exts (IsList(..))
import Control.Carrier.NonDet.Church (runNonDet, NonDetC (..), runNonDetA)
import Control.Effect.Fresh (Fresh)
import Language.Haskell.TH (Q, Exp, lamE, varE, appE, newName, varP)
import Control.Carrier.Reader (runReader)
import Data.Kind (Type)
import Dentrado.POC.Memory (Res (..), Cast (..), Container (..), AppIO, Reduce' (..), Delay (..), ReduceC, AppIOC, AppForce(..), Reduce, RevList, AppDelay(..), Reduce'C (..), allocC, mkReducible, tryFetchC, reduce', runReduce, fetchC, reducible, revSnoc, sNothing, fetch, unwrap, mkDelayCache, runReduce', alloc, reducible', builtin, Ser, ResB (..), wrapB, (:->) (..), delayAppBuiltinFun, DelayApp (..), M (..), C (..), InferValT, InferContainerT, Serialized (..), SerializedGearFn (..), mkDelayLazy)
import Control.Effect.Writer (tell)
import Dentrado.POC.Types (Chunk, RadixTree (..), RadixChunk, RadixChunk' (..), readReducible, EventId (EventId), Timestamp (..), LocalId (..), MapDiffE (..))
import qualified Data.ByteString as B
import qualified Data.ByteString.Unsafe as B
import qualified Data.ByteString.Builder as B
import qualified RIO.NonEmpty as NE
import Control.Effect.Empty (Empty (..))
import Data.Coerce (coerce)
import Control.Monad.Free (Free (..))
import Data.Functor.Compose (Compose (..))

$(moduleId 1)

-- TODO: path compression for really long unique keys
-- TODO: proper church encoding.
-- TODO: is fusion (merge-filter-map) possible? with delays?..
-- TODO: Oh my god, this is so bad. `join` violates the behaviour of Reducible. This urgently needs to be
-- church/zipper made.

class IsRadixKey key where
  toRadixKey :: key -> [Chunk]
  fromRadixKey :: [Chunk] -> key
  -- LAW: a `compare` b = toRadixKey a `compare` toRadixKey b

instance IsRadixKey [Chunk] where
  toRadixKey = id
  fromRadixKey = id
instance IsRadixKey Chunk where
  toRadixKey = pure
  fromRadixKey = \case
    [x] -> x
    _ -> error "key corrupted"

-- TODO: UNSAFE
-- Deal with it when implementing deduplication
-- instance IsRadixKey ByteString where
instance IsRadixKey (Serialized a) where
  toRadixKey = \(UnsafeSerialized x) -> f x where
    f (B.null -> True) = []
    f b =
      let x =
            (fromIntegral @_ @Word32 (b `B.unsafeIndex` 0) `unsafeShiftL` 24) .|.
            (fromIntegral @_ @Word32 (b `B.unsafeIndex` 1) `unsafeShiftL` 16) .|.
            (fromIntegral @_ @Word32 (b `B.unsafeIndex` 2) `unsafeShiftL`  8) .|.
            fromIntegral @_ @Word32 (b `B.unsafeIndex` 3)
      in x : f (B.drop 4 b)
  fromRadixKey =
    UnsafeSerialized . toStrictBytes . B.toLazyByteString . mconcat . fmap B.word32BE
instance IsRadixKey (SerializedGearFn) where
  toRadixKey (SerializedGearFn x) = toRadixKey x
  fromRadixKey = SerializedGearFn . fromRadixKey

instance IsRadixKey EventId where
  toRadixKey (EventId (Timestamp a) (LocalId b)) = [a, b]
  fromRadixKey = \case
    [a, b] -> EventId (Timestamp a) (LocalId b)
    _ -> error "key corrupted"

instance IsRadixKey [EventId] where
  toRadixKey = concatMap toRadixKey
  fromRadixKey = \case
    (a:b:xs) -> fromRadixKey @EventId [a, b] : fromRadixKey @[EventId] xs
    [] -> []
    _ -> error "key corrupted"


tryMask :: Chunk -> Chunk -> Maybe Bool
tryMask mask key =
  if prefixBits .&. mask == prefixBits .&. key
  then Just $ 1 .&. (key `unsafeShiftR` countTrailingZeros mask) == 1
  else Nothing
  where
    prefixBits = complement $ mask - 1 `xor` mask
{-# INLINE tryMask #-}

makeMask :: Chunk -> Chunk -> (Chunk, Bool)
makeMask l r =
  let maskBit = unsafeShiftL 1 (finiteBitSize (0 :: Chunk) - 1 - countLeadingZeros (l `xor` r))
  in (maskBit .|. (l .&. complement (maskBit-1)), r .&. maskBit /= 0)

-- TODO: Implement Zebra simply by adding metadata field to Nil
-- Justification: RadixTree stores discrete and continuous data,
-- with discrete data being saved in Tip and continuous data being
-- saved in Nil. Typically the only continuous data that we work with
-- is "there's nothing here in this continuous region".
-- But this could be repurposed to store more cases.


-- aliases

type Map = RadixTree
type MapR = Map Res
type Set = RadixTree
type SetR k = MapR k ()

unMapDiffE :: MapDiffE v -> (Maybe v, Maybe v)
unMapDiffE = \case
  MapDel v -> (Just v, Nothing)
  MapUpd v1 v2 -> (Just v1, Just v2)
  MapAdd v -> (Nothing, Just v)
{-# INLINE unMapDiffE #-}

fromMapDiffE :: v -> MapDiffE v -> (v, v)
fromMapDiffE def = bimap (fromMaybe def) (fromMaybe def) . unMapDiffE
{-# INLINE fromMapDiffE #-}

hdlMapDiffE :: Monad m => (v -> a -> m a) -> (v -> a -> m a) -> MapDiffE v -> a -> m a
hdlMapDiffE onDel onAdd (unMapDiffE -> (del, add)) =
  maybe pure onAdd add <=< maybe pure onDel del
{-# INLINE hdlMapDiffE #-}

mkMapDiffE :: Maybe a -> Maybe a -> Maybe (MapDiffE a)
mkMapDiffE a b = case (a, b) of
  (Nothing, Nothing) -> Nothing
  (Nothing, Just b') -> Just $ MapAdd b'
  (Just a', Nothing) -> Just $ MapDel a'
  (Just a', Just b') -> Just $ MapUpd a' b'

data SetDiffE = SetAdd | SetDel

instance Cast (MapDiffE ()) (Maybe SetDiffE) where
  cast = \case
    MapAdd () -> Just SetAdd
    MapUpd () () -> Nothing
    MapDel () -> Just SetDel

sNil :: ResB (RadixChunk c2 k a)
sNil = $sFreshI $ builtin $ mkReducible Nil

-- -- TODO: Don't know how effective is this
reduceChunk'' :: (Container c, Has (AppIO :+: Reduce' s) sig m) => Proxy s -> RadixChunk' c k a -> m (RadixChunk' c k a, Maybe (c (RadixChunk c k a)))
reduceChunk'' (Proxy @s) = \case
  Tip _ (RadixTree (tryFetchC -> Just Nothing) (tryFetchC -> Just (readReducible -> Nil))) -> reduce' (Proxy @s) $> (Nil, Just $ wrapB sNil)
  Bin _ left'@(tryFetchC -> Just (readReducible -> left)) right'@(tryFetchC -> Just (readReducible -> right))
    | Nil <- left -> reduce' (Proxy @s) $> (right, Just right') -- hopefully no need to reduceChunk left/right
    | Nil <- right -> reduce' (Proxy @s) $> (left, Just left')
  nonReducible -> pure (nonReducible, Nothing)
{-# INLINE reduceChunk'' #-}

reduceChunk' :: (Container c, Has (AppIO :+: Reduce' s) sig m) => Proxy s -> RadixChunk' c k a -> m (RadixChunk' c k a)
reduceChunk' p v = fst <$> reduceChunk'' p v
{-# INLINE reduceChunk' #-}

reduceChunk :: (Container c, Has (AppIO :+: Reduce) sig m) => RadixChunk' c k a -> m (RadixChunk' c k a)
reduceChunk = reduceChunk' (Proxy @"")
{-# INLINE reduceChunk #-}

allocReducedChunk :: (Container c1, Container c2, Has AppIO sig m, Ser a, Typeable k) => (forall b. c2 b -> ReduceC m (c1 b)) -> RadixChunk' c2 k a -> m (c1 (RadixChunk c2 k a))
allocReducedChunk f c = runReduce $ reduceChunk'' (Proxy @"") c >>= \case
  (v, Nothing) -> allocC $ mkReducible v
  (_, Just v) -> f v
{-# INLINE allocReducedChunk #-}

data SChunk
data STree

-- in SelBin, returning new seelector is superfluous, we could just use previous one
newtype FinalPath = FinalPath [Chunk]
class Selector s m where
  selTree :: Ser a => Container c => s k STree -> c (Maybe a) -> m (Maybe (s k SChunk))
  selBin :: s k SChunk -> Chunk -> m (Maybe (Bool, s k SChunk))
  selTip :: s k SChunk -> Chunk -> m (Maybe (s k STree))
  selNil :: s k SChunk -> m (Chunk, [Chunk])

accessRadix :: forall sel c k a tree chunk sig m. (Selector sel m, Container c, Has (AppIO :+: Reduce) sig m, Typeable k, Ser a)
  => (c (Maybe a) -> chunk -> tree) -- ^ on sub, tree
  -> (FinalPath -> RadixTree c k a -> tree) -- ^ on found, tree
  -> (Chunk -> [Chunk] -> FinalPath -> chunk) -- ^ on missing, chunk
  -> (Chunk -> tree -> chunk) -- ^ on Tip, chunk
  -> (Bool -> Chunk -> c (RadixChunk c k a) -> chunk -> chunk) -- ^ on branch, chunk
  -> (RevList Chunk -> sel k SChunk -> c (RadixChunk c k a) -> m chunk, RevList Chunk -> sel k STree -> RadixTree c k a -> m tree)
accessRadix onSubT onFoundT onMissingC onTipC onBranchC =
  let
    goChunk :: RevList Chunk -> sel k SChunk -> c (RadixChunk c k a) -> m chunk
    goChunk path sel1 chunkM =
      let
        selNil' = do
          (k, ks) <- selNil sel1
          pure (k, onMissingC k ks (FinalPath $ toList path <> [k] <> ks))
        newBranch :: Chunk -> m chunk
        newBranch exKey = do
          (key, missing) <- selNil'
          let (mask, placeRight) = makeMask exKey key
          pure $ onBranchC placeRight mask chunkM missing
      in fetchC chunkM >>= \chunk -> reducible reduceChunk chunk \case
        Nil -> snd <$> selNil'
        (Tip key subtree) -> selTip sel1 key >>= \case
          Nothing -> newBranch key
          Just sel2 -> onTipC key <$> goTree (path `revSnoc` key) sel2 subtree
        (Bin mask l r) -> selBin sel1 mask >>= \case
          Nothing -> newBranch mask
          Just (pickRight, sel2) -> onBranchC pickRight mask (if pickRight then l else r) <$> goChunk path sel2 (if pickRight then r else l)
    goTree :: RevList Chunk -> sel k STree -> RadixTree c k a -> m tree
    goTree path sel1 rt@(RadixTree val chunk) = selTree sel1 val >>= \case
      Nothing -> pure $ onFoundT (FinalPath $ toList path) rt
      Just sel2 -> onSubT val <$> goChunk path sel2 chunk
  in (goChunk, goTree)
{-# INLINE accessRadix #-}

mkBinNonRe :: Container c => Bool -> Chunk -> c (RadixChunk c k a) -> c (RadixChunk c k a) -> RadixChunk' c k a
mkBinNonRe right mask a b = Bin mask (if right then a else b) (if right then b else a)
{-# INLINE mkBinNonRe #-}

mkBin :: (Container c1, Container c2, Has AppIO sig m, Ser a, Typeable k)  => (forall b. c2 b -> ReduceC m (c1 b)) -> Bool -> Chunk -> c2 (RadixChunk c2 k a) -> c2 (RadixChunk c2 k a) -> m (c1 (RadixChunk c2 k a))
mkBin f a b c d = allocReducedChunk f $ mkBinNonRe a b c d
{-# INLINE mkBin #-}

mkTipNonRe :: Chunk -> RadixTree c k a -> RadixChunk' c k a
mkTipNonRe = Tip

mkTip :: (Container c1, Container c2, Has AppIO sig m, Ser a, Typeable k) => (forall b. c2 b -> ReduceC m (c1 b)) -> Chunk -> RadixTree c2 k a -> m (c1 (RadixChunk c2 k a))
mkTip f k v = allocReducedChunk f $ mkTipNonRe k v
{-# INLINE mkTip #-}

internalLookup :: (Has (AppIO :+: Reduce) sig m, Selector sel m, Container c, IsRadixKey k, Ser a, Typeable k) => (RevList Chunk -> sel k SChunk -> c (RadixChunk c k a) -> m (m (Maybe (k, a))), RevList Chunk -> sel k STree -> RadixTree c k a -> m (m (Maybe (k, a))))
internalLookup = accessRadix
  (\_ -> id)
  (\(FinalPath k) (RadixTree a _) -> ((fromRadixKey k,) <$>) <$> fetchC a)
  (\_ _ _ -> pure Nothing)
  (\_ -> id)
  (\_ _ _ -> id)
{-# INLINE internalLookup #-}

lookupKV :: (Has AppIO sig m, Selector sel (ReduceC m), Container c, IsRadixKey k, Ser a, Typeable k) => sel k STree -> RadixTree c k a -> m (Maybe (k, a))
lookupKV k tr = runReduce $ join $ snd internalLookup [] k tr

lookup :: (Has AppIO sig m, Selector sel (ReduceC m), Container c, IsRadixKey k, Ser a, Typeable k) => sel k STree -> RadixTree c k a -> m (Maybe a)
lookup k tr = fmap snd <$> lookupKV k tr

internalNested :: (Ser a, Container c, Algebra sig m, Has AppIO sig m, Typeable k) => c (Maybe a) -> [Chunk] -> m (c (RadixChunk c k a))
internalNested finalVal ks = do
  (_state, res) <- foldrM
    (\key (subval, subchunk) ->
      (wrapB sNothing,) <$> allocC (mkReducible $ mkTipNonRe key $ RadixTree subval subchunk)) -- unlikely reduced
    (finalVal, wrapB sNil)
    ks
  pure res

internalInsert :: forall sel c k sig m a. (Selector sel m, Container c, Has (AppIO :+: Reduce) sig m, Ser a, Typeable k) => a -> (RevList Chunk -> sel k SChunk -> c (RadixChunk c k a) -> m (m (c (RadixChunk c k a))), RevList Chunk -> sel k STree -> RadixTree c k a -> m (m (RadixTree c k a)))
internalInsert val = accessRadix
  (\a b -> RadixTree a <$> b)
  (\_ (RadixTree _oldVal b) -> (`RadixTree` b) <$> allocC (Just val))
  (\key1 keys2 _ -> (`internalNested` (key1:keys2)) =<< allocC (Just val))
  (\k v -> allocC . mkReducible . mkTipNonRe k =<< v)
  (\k r a b -> allocC . mkReducible . mkBinNonRe k r a =<< b)
{-# INLINE internalInsert #-}

-- short-circuit
insert :: (Selector sel (ReduceC m), Container c, Has AppIO sig m, Ser p, Typeable k) => sel k STree -> p -> RadixTree c k p -> m (RadixTree c k p)
insert k v tr = runReduce $ join $ snd (internalInsert v) [] k tr

-- could be m (f (...)), but I don't think it's worth it
-- edit: probably needed, but probably overshadowed by the Church theme
internalUpdate :: (Selector sel m, Container c, Has (AppIO :+: Reduce) sig m, Ser a, Typeable k)
  => (c (Maybe a) -> m (c (Maybe a))) -> (RevList Chunk -> sel k SChunk -> c (RadixChunk c k a) -> m (m (c (RadixChunk c k a))), RevList Chunk -> sel k STree -> RadixTree c k a -> m (m (RadixTree c k a)))
internalUpdate f = accessRadix
  (\a b -> RadixTree a <$> b) -- on sub, tree
  (\_ (RadixTree updated sub) -> (`RadixTree` sub) <$> f updated) -- on found, tree
  (\key1 keys2 _ -> do
    val <- f $ wrapB sNothing
    if (val `same` (wrapB sNothing))
      then pure $ wrapB sNil
      else internalNested val (key1:keys2)
    )
  (\key tree -> mkTip pure key =<< tree) -- on Tip, chunk
  (\k r a b -> mkBin pure k r a =<< b) -- on branch, chunk
{-# INLINE internalUpdate #-}

-- short-circuit?
update :: (Selector sel (ReduceC m), Container c, Has AppIO sig m, Ser a, Typeable k) => (c (Maybe a) -> ReduceC m (c (Maybe a))) -> sel k STree -> RadixTree c k a -> m (RadixTree c k a)
update f k tr = runReduce $ join $ snd (internalUpdate f) [] k tr

-- short-circuit
delete :: (Selector sel (ReduceC m), Container c, Has AppIO sig m, Ser a, Typeable k) => sel k STree -> RadixTree c k a -> m (RadixTree c k a)
delete = update (\_ -> pure $ wrapB sNothing)

pop :: (Selector sel (ReduceC (WriterC (First a) m)), Container c, Has AppIO sig m, Ser a, Typeable k) => sel k STree -> RadixTree c k a -> m (Maybe a, RadixTree c k a)
pop k rt = runWriter (\(First a) b -> pure (a, b)) $ update
  (\v -> do
    v' <- fetchC v
    tell $ First v'
    pure $ wrapB sNothing
  )
  k rt

upsertChurchInternal ::
  (Selector sel (ReduceC m), Container c, Has AppIO sig m, Ser a, Typeable k, IsRadixKey k) =>
    (RevList Chunk -> sel k SChunk -> c (RadixChunk c k a) -> ReduceC m (  ReduceC m (Maybe (k, a)), a -> m (c (RadixChunk c k a)) )
    , RevList Chunk -> sel k STree -> RadixTree c k a -> ReduceC m (  ReduceC m (Maybe (k, a)), a -> m (RadixTree c k a) ))
-- actually the snd part could work with any other monad, but I'm afraid to break the specialization at any step, needs testing.
upsertChurchInternal = accessRadix
  (\a (lookRes, ins) -> (lookRes, \newVal -> RadixTree a <$> ins newVal)) -- on sub, tree
  (\(FinalPath k) (RadixTree exVal sub) -> (fmap (fromRadixKey k,) <$> fetchC exVal, \newVal -> (`RadixTree` sub) <$> allocC (Just newVal))) -- on found, tree
  (\k1 ks _ -> (pure Nothing, (`internalNested` (k1:ks)) <=< allocC . Just)) -- on missing, chunk
  (\key (lookRes, ins) -> (lookRes, \newVal -> mkTip pure key =<< ins newVal)) -- on Tip, chunk
  (\k r a (lookRes, ins) -> (lookRes, \newVal -> mkBin pure k r a =<< ins newVal)) -- on branch, chunk
{-# INLINE upsertChurchInternal #-}

upsertChurch :: (Container c, Has AppIO sig m, Selector sel (ReduceC m), Ser a, Typeable k, IsRadixKey k) => sel k STree -> RadixTree c k a -> m (Maybe a, a -> m (RadixTree c k a))
upsertChurch sel tree = runReduce do
  (lookRes1M, ins1) <- snd upsertChurchInternal [] sel tree
  lookRes1 <- lookRes1M
  pure (snd <$> lookRes1, ins1)

-- misc

-- TODO: in some places we implicitly allocC. Shouldn't all allocations be performed by the end-user?
-- TODO: prepF hurts performance, we should get rid of it if possible.
-- TODO: move onTree/onBin/onTip/onNil to strategy
class (Container c, Container cfin) => AppWither strat m c cfin where
  -- stratWither :: strat -> ResB (Res a :-> ReduceC m (Res b)) -> c a -> ReduceC m (cfin b)
  stratWitherLift :: (Has Fresh sig2 m2, InferValT a, InferValT b) => strat -> (Res a -> ReduceC m (Res b)) -> m2 (c a -> ReduceC m (cfin b))

instance (Has AppIO sig m, Container c, Container cfin) => AppWither AppForce m c cfin where
  stratWitherLift _ f = pure \a -> do
    a' <- unwrap a
    wrap <$> f a'

instance AppWither AppDelay AppIOC Delay Delay where
  stratWitherLift _ f = do
    preparedF <- delayAppBuiltinFun . FunBuiltin =<< builtin (M . fmap C . runReduce . f . unC)
    pure \a -> mkDelayCache (preparedF `DelayApp` a)

witherF :: forall tree chunk sig1 m1 sig2 m2 strat c cfin k a b.
  (Has Fresh sig1 m1, MonadFix m1, AppWither strat m2 c cfin, InferValT a, InferValT b, Ser a, Has AppIO sig2 m2, Typeable k, InferValT chunk, InferValT k, InferContainerT c)
  => (cfin (Maybe b) -> cfin chunk -> m2 tree)
  -> (Bool -> Chunk -> cfin chunk -> cfin chunk -> m2 (Res chunk))
  -> (Chunk -> tree -> m2 (Res chunk))
  -> m2 (Res chunk)
  -> strat
  -> (Res (Maybe a) -> a -> ReduceC m2 (Res (Maybe b)))
  -> m1 (c (RadixChunk c k a) -> ReduceC m2 (cfin chunk), RadixTree c k a -> m2 tree) -- impredicativity
witherF onTree onBin onTip onNil strat f = mdo
  goVal <- stratWitherLift strat \vR -> do
    vM <- fetch vR
    case vM of
      Nothing -> pure $ ResBuiltin sNothing
      Just v -> f vR v
  goChunk <- stratWitherLift strat \chunkRes -> do
    chunkRed <- fetch chunkRes
    reducible reduceChunk chunkRed \case
      Tip mask v -> do
        t <- goTree v
        lift $ onTip mask t
      Bin mask l r -> do
        (l', r') <- (,) <$> goChunk l <*> goChunk r
        lift $ onBin True mask l' r'
      Nil -> lift onNil
  let
    goTree :: RadixTree c k a -> ReduceC m2 tree
    goTree (RadixTree vC subC) = do
      (a, b) <- (,)
        <$> goVal vC
        <*> goChunk subC
      lift $ onTree a b
  pure (goChunk, runReduce . goTree)

wither :: forall sig1 m1 sig2 m2 strat c cfin k a b.
  (Has Fresh sig1 m1, MonadFix m1, Has AppIO sig2 m2, AppWither strat m2 c cfin, Ser b, Ser a, Typeable k, InferValT b, InferValT a, InferValT k, InferContainerT cfin, InferContainerT c)
  => strat
  -> (Res (Maybe a) -> a -> ReduceC m2 (Res (Maybe b)))
  -> m1 (c (RadixChunk c k a) -> ReduceC m2 (cfin (RadixChunk cfin k b)), RadixTree c k a -> m2 (RadixTree cfin k b)) -- impredicativity
wither = witherF (\a b -> pure $ RadixTree a b) (mkBin unwrap) (mkTip unwrap) (pure $ ResBuiltin sNil)

sWither :: Q Exp
sWither = do
  strat <- newName "strat"
  f <- newName "f"
  [varP strat, varP f] `lamE` (
      varE 'snd `appE` (sFreshI `appE` (varE 'wither `appE` varE strat `appE` varE f))
    )

data OnOne chunk (m :: Type -> Type) c k this fin = OnOne
  { onOneVal :: !(Res (Maybe this) -> this -> m (Res (Maybe fin))) -- this must be unwrapped for this conclusion
  , onOneSubtree :: !(Res (RadixChunk c k this) -> ReduceC m (Res chunk)) }
newtype OnBoth m one two fin = OnBoth
  { onBothVal :: Res (Maybe one) -> one -> Res (Maybe two) -> two -> m (Res (Maybe fin)) }
data OnSame chunk m c cfin k one two fin = OnSame
  { onSameVal :: !(c (Maybe one) -> c (Maybe two) -> m (cfin (Maybe fin)))
  , onSameValR :: !(Res (Maybe one) -> Res (Maybe two) -> m (Res (Maybe fin)))
  , onSameSubtree :: !(c (RadixChunk c k one) -> c (RadixChunk c k two) -> m (cfin chunk))
  , onSameSubtreeR :: !(Res (RadixChunk c k one) -> Res (RadixChunk c k two) -> m (Res chunk)) }

class (Container c, Container cfin) => AppMerge strat m c cfin where
  -- stratMerge :: strat -> Res (Res x -> Res y -> Reduce'C "1" (Reduce'C "2" m) (Res z)) -> c x -> c y -> Reduce'C "1" (Reduce'C "2" m) (cfin z)
  stratMergeLift :: (Has Fresh sig2 m2, InferValT x, InferValT y, InferValT z)
    => strat -> (Res x -> Res y -> Reduce'C "1" (Reduce'C "2" m) (Res z)) -> m2 (c x -> c y -> Reduce'C "1" (Reduce'C "2" m) (cfin z))

instance (Has AppIO sig m, Container c, Container cfin) => AppMerge AppForce m c cfin where
  stratMergeLift _ f = pure \a b ->
    wrap <$> join (f <$> unwrap' (Proxy @"1") a <*> unwrap' (Proxy @"2") b)

instance AppMerge AppDelay AppIOC Delay Delay where
  stratMergeLift _ f = do
    preparedF <- delayAppBuiltinFun . FunCurry . FunBuiltin =<< builtin \(C a, C b) -> M $
      fmap C $ runReduce' @"2" $ runReduce' @"1" $ f a b
    pure \a b -> mkDelayCache (preparedF `DelayApp` a `DelayApp` b)
 

reduce1 :: Algebra sig m => ReduceC m a -> Reduce'C "1" (Reduce'C "2" m) a
reduce1 (Reduce'C act) = do
  flag <- send $ GetReduce' @"1"
  lift $ lift $ runReader flag act

reduce2 :: Algebra sig m => ReduceC m a -> Reduce'C "1" (Reduce'C "2" m) a
reduce2 (Reduce'C act) = do
  flag <- send $ GetReduce' @"2"
  lift $ lift $ runReader flag act

-- I believe there is a problem with how mergeF handles references and containers. It performs some destructive wraps and unwraps here and there.
mergeF :: forall sig1 m1 sig2 m2 strat c cfin k one two fin chunk tree.
  (Has Fresh sig1 m1, MonadFix m1, AppMerge strat m2 c cfin, Has AppIO sig2 m2
  , InferContainerT c, InferValT one, InferValT two, InferValT fin, InferValT chunk, InferValT k, Typeable k
  , Ser one, Ser two)
  => (cfin (Maybe fin) -> cfin chunk -> m2 tree)
  -> (Bool -> Chunk -> cfin chunk -> cfin chunk -> m2 (Res chunk))
  -> (Chunk -> tree -> m2 (Res chunk))
  -> strat
  -> OnOne chunk m2 c k one fin
  -> OnOne chunk m2 c k two fin
  -> OnBoth m2 one two fin
  -> Maybe (OnSame chunk m2 c cfin k one two fin)
  -> m1 (RadixTree c k one
    -> RadixTree c k two
    -> m2 tree)
mergeF onTree onBin onTip strat one1 one2 both sameM = mdo
  let
    checkSame :: forall c2 a b w. Container c2 => c2 a -> c2 b -> (OnSame chunk m2 c cfin k one two fin -> w) -> w -> w
    checkSame = case sameM of
        Just hdl -> \a b h o -> if a `same` b
          then h hdl
          else o
        Nothing -> \_ _ _ o -> o
    checkSameMergeChunk a b = checkSame a a (\s -> lift $ lift $ onSameSubtree s a b) (mergeChunk a b)
  mergeVal <- stratMergeLift strat \r1 r2 -> do
    checkSame r1 r2
      (\s -> lift $ lift $ onSameValR s r1 r2)
      do
        v1 <- fetch r1
        v2 <- fetch r2
        lift $ lift $ case (v1, v2) of
          (Just a , Just b ) -> onBothVal both r1 a r2 b
          (Just a , Nothing) -> onOneVal one1 r1 a
          (Nothing, Just b ) -> onOneVal one2 r2 b
          (Nothing, Nothing) -> pure $ ResBuiltin sNothing
  mergeChunk  <- stratMergeLift strat \res1 res2 ->
    checkSame
      res1
      res2
      (\s -> lift $ lift $ onSameSubtreeR s res1 res2)
      do
        v1 <- fetch res1
        v2 <- fetch res2
        let binOfMerges mask a1 a2 b1 b2 = do
              (a, b) <- (,) <$> checkSameMergeChunk a1 a2 <*> checkSameMergeChunk b1 b2
              lift $ lift $ onBin True mask a b
            unrelated key1 key2 = do
              let (mask, pickRight) = makeMask key1 key2
              (a, b) <- (,) <$> reduce1 (onOneSubtree one1 res1) <*> reduce2 (onOneSubtree one2 res2)
              lift $ lift $ onBin pickRight mask (wrap a) (wrap b)
            oneContainsTwo mask1 key2 l1 r1 = case tryMask mask1 key2 of
              Just True  -> binOfMerges mask1 l1 (wrapB sNil) r1 (wrap res2)
              Just False -> binOfMerges mask1 l1 (wrap res2) r1 (wrapB sNil)
              Nothing -> unrelated mask1 key2
            twoContainsOne key1 mask2 l2 r2 = case tryMask mask2 key1 of
              Just False -> binOfMerges mask2 (wrap res1) l2 (wrapB sNil) r2
              Just True  -> binOfMerges mask2 (wrapB sNil) l2 (wrap res1) r2
              Nothing -> unrelated mask2 key1
        reducible' (Proxy @"1") (reduceChunk' (Proxy @"1")) v1 \v1' ->
          reducible' (Proxy @"2") (reduceChunk' (Proxy @"2")) v2 \v2' ->
            case (v1', v2') of
              (_, Nil) -> reduce1 $ onOneSubtree one1 res1
              (Nil, _) -> reduce2 $ onOneSubtree one2 res2
              (Bin mask1 l1 r1, Bin mask2 l2 r2)
                | mask1 == mask2 -> binOfMerges mask1 l1 l2 r1 r2
                | otherwise -> if countTrailingZeros mask1 >= countTrailingZeros mask2
                  then oneContainsTwo mask1 mask2 l1 r1
                  else twoContainsOne mask1 mask2 l2 r2
              (Bin mask1 l1 r1, Tip key2 _) -> oneContainsTwo mask1 key2 l1 r1
              (Tip key1 _, Bin mask2 l2 r2) -> twoContainsOne key1 mask2 l2 r2
              (Tip key1 l, Tip key2 r)
                | key1 == key2 -> do
                  t <- mergeTree l r
                  lift $ lift $ onTip key1 t
                | otherwise -> unrelated key1 key2
  let mergeTree (RadixTree k1 s1) (RadixTree k2 s2) = do
        (a, b) <- (,)
          <$> checkSame k1 k2 (\s -> lift $ lift $ onSameVal s k1 k2) (mergeVal k1 k2)
          <*> checkSameMergeChunk s1 s2
        lift $ lift $ onTree a b
  pure \a b -> runReduce' @"2" $ runReduce' @"1" $ mergeTree a b

merge ::
  (Has Fresh sig1 m1, MonadFix m1, AppMerge strat m2 c cfin, Has AppIO sig2 m2
  , InferContainerT c, InferContainerT cfin, InferValT one, InferValT two, InferValT fin, InferValT k, Typeable k
  , Ser one, Ser two, Ser fin)
  => strat
  -> OnOne (RadixChunk cfin k fin) m2 c k one fin
  -> OnOne (RadixChunk cfin k fin) m2 c k two fin
  -> OnBoth m2 one two fin
  -> Maybe (OnSame (RadixChunk cfin k fin) m2 c cfin k one two fin)
  -> m1 (RadixTree c k one
    -> RadixTree c k two
    -> m2 (RadixTree cfin k fin))
merge = mergeF (\a b -> pure $ RadixTree a b) (mkBin unwrap) (mkTip unwrap)

-- suggestion: remove that
{-
sMerge :: Q Exp
sMerge = do
  strat <- newName "strat"
  one1 <- newName "one1"
  one2 <- newName "one2"
  both <- newName "both"
  sameM <- newName "sameM"
  [varP strat, varP one1, varP one2, varP both] `lamE` (
      sFreshI `appE` (
        varE 'merge `appE`
        varE strat `appE`
        varE one1 `appE`
        varE one2 `appE`
        varE both `appE`
        varE sameM)
    )
-}

onOneErase :: Applicative m => OnOne (RadixChunk c2 k1 a) m c1 k2 this fin
onOneErase = OnOne (const $ const $ pure $ wrapB sNothing) (const $ pure $ wrapB sNil)

-- TODO: get rid of alloc's, first of all by creating a Maybe (Rec a) ~ Rec (Maybe a) isomorphism?
onOneKeep :: Applicative m => OnOne (RadixChunk c k fin) m c k fin fin
onOneKeep = OnOne (const . pure) pure

onBothZip :: (Has AppIO sig m, Ser fin) => (one -> two -> Maybe fin) -> OnBoth m one two fin
onBothZip f = OnBoth \_ one _ two -> alloc $ f one two

onOneWitherFM ::
  (Has Fresh sig1 m1, MonadFix m1, Container c, AppWither strat m2 c cfin, Has AppIO sig2 m2,
  InferContainerT c, InferValT b, InferValT a, InferValT chunk, InferValT k, Typeable k,
  Ser a)
  => (cfin (Maybe b) -> cfin chunk -> m2 tree)
  -> (Bool -> Chunk -> cfin chunk -> cfin chunk -> m2 (Res chunk))
  -> (Chunk -> tree -> m2 (Res chunk))
  -> m2 (Res chunk)
  -> strat
  -> (Res (Maybe a) -> a -> m2 (Res (Maybe b))) -> m1 (OnOne chunk m2 c k a b)
onOneWitherFM onTree onBin onTip onNil strat f = do
  toFin <- fst <$> witherF onTree onBin onTip onNil strat \x y -> lift (f x y)
  pure $ OnOne f \chunk -> toFin (wrap chunk) >>= unwrap

onOneWitherM :: (Has Fresh sig m, MonadFix m, Container c, Has AppIO sig2 m2, AppWither strat m2 c cfin, Ser this, InferContainerT c, InferContainerT cfin, InferValT fin, InferValT this, InferValT k, Typeable k, Ser fin)
  => strat -> (Res (Maybe this) -> this -> m2 (Res (Maybe fin))) -> m (OnOne (RadixChunk cfin k fin) m2 c k this fin)
onOneWitherM = onOneWitherFM (\a b -> pure $ RadixTree a b) (mkBin unwrap) (mkTip unwrap) (pure $ wrapB sNil)

-- mergeWithUpdate :: forall c sig1 m1 sig2 m2 k fin upd.
--   (Container c, Has Fresh sig1 m1, MonadFix m1, Has AppIO sig2 m2, Ser fin, InferValT k, InferValT upd, InferValT fin, InferContainerT c, Ser upd, Typeable k)
--   => (Maybe fin -> upd -> fin)
--   -> m1 (RadixTree c k fin
--     -> RadixTree c k upd
--     -> m2 (RadixTree c k fin))
-- mergeWithUpdate f = do
--     w <- onOneWitherM AppForce $ const $ alloc . Just . f Nothing
--     merge AppForce onOneKeep w
--       (OnBoth \_ fin _ upd -> allocC $ Just $ f (Just fin) upd)
--       Nothing

mergeId :: (Ser a, Ser this, InferValT k, InferValT this, InferValT a,  InferContainerT cfin, InferContainerT c, AppWither p m2 c cfin,  AppMerge p m2 c cfin, Has AppIO sig m2, Typeable k) =>
  p -> RadixTree c k this -> RadixTree c k a -> m2 (RadixTree cfin k (Maybe this, Maybe a))
mergeId strat = $sFreshI do
  o1 <- onOneWitherM strat \_ -> allocC . Just . (, Nothing) . Just
  o2 <- onOneWitherM strat \_ -> allocC . Just . (Nothing,) . Just
  merge strat o1 o2 (OnBoth \_ a _ b -> allocC $ Just (Just a, Just b)) Nothing

-- diff

diffF ::
  (Has Fresh sig1 m1, MonadFix m1, AppMerge strat m2 c cfin, AppWither strat m2 c cfin, Has AppIO sig2 m2, InferContainerT c, InferValT fin, InferValT a, InferValT chunk, InferValT k, Ser a, Typeable k)
  => (cfin (Maybe fin) -> cfin chunk -> m2 tree)
  -> (Bool -> Chunk -> cfin chunk -> cfin chunk -> m2 (Res chunk))
  -> (Chunk -> tree -> m2 (Res chunk))
  -> m2 (Res chunk)
  -> strat
  -> (MapDiffE a -> m2 (Res (Maybe fin)))
  -> m1 (RadixTree c k a -> RadixTree c k a -> m2 tree)
diffF onTree onBin onTip onNil strat f = do
  w1 <- onOneWitherFM onTree onBin onTip onNil strat \_ x -> f (MapDel x)
  w2 <- onOneWitherFM onTree onBin onTip onNil strat \_ x -> f (MapAdd x)
  mergeF onTree onBin onTip strat w1 w2
    (OnBoth \_ a _ b -> f (MapUpd a b))
    (Just $ OnSame (\_ _ -> pure $ wrapB sNothing) (\_ _ -> pure $ wrapB sNothing) (\_ _ -> wrap <$> onNil) (\_ _ -> onNil))

diff :: (Has Fresh sig1 m1, MonadFix m1, AppMerge strat m2 c cfin, AppWither strat m2 c cfin, Has AppIO sig2 m2, Ser a, InferContainerT c, InferContainerT cfin, InferValT fin, InferValT a, InferValT k, Typeable k, Ser fin)
  => strat
  -> (MapDiffE a -> m2 (Res (Maybe fin)))
  -> m1 (RadixTree c k a -> RadixTree c k a -> m2 (RadixTree cfin k fin))
diff = diffF (\a b -> pure $ RadixTree a b) (mkBin unwrap) (mkTip unwrap) (pure $ wrapB sNil)

diffId ::
  (Ser a, Ser (MapDiffE a), InferValT k, InferValT a, InferValT (MapDiffE a), InferContainerT cfin, InferContainerT c, AppWither strat m2 c cfin, AppMerge strat m2 c cfin, Has AppIO sig m2, Typeable k) =>
  strat -> RadixTree c k a -> RadixTree c k a -> m2 (RadixTree cfin k (MapDiffE a))
diffId strat = $sFreshI $ diff strat $ alloc . Just

intersection :: (AppMerge p m c2 c2, Has AppIO sig m, InferContainerT c2, InferValT two, InferValT fin,  InferValT k2, Ser two, Ser fin, Typeable k2) => p -> RadixTree c2 k2 fin -> RadixTree c2 k2 two -> m (RadixTree c2 k2 fin)
intersection strat = $sFreshI $ merge strat onOneErase onOneErase (OnBoth \a _ _ _ -> pure a) $ Just $
  OnSame (\l _ -> pure l) (\l _ -> pure l) (\l _ -> pure l) (\l _ -> pure l)

-- selectors

data family SelEq k t -- access equal to key

newtype instance SelEq k STree = SelEqT [Chunk]
data instance SelEq k SChunk = SelEqC !Chunk ![Chunk]

instance Applicative m => Selector SelEq m where
  selTree (SelEqT keys) _val = pure case keys of
    [] -> Nothing
    k:ks-> Just $ SelEqC k ks
  selBin (SelEqC key keys) mask = pure $ (, SelEqC key keys) <$> tryMask mask key
  selTip (SelEqC key keys) key2 = pure $ if key == key2 then Just (SelEqT keys) else Nothing
  selNil (SelEqC key keys) = pure (key, keys)

selEq :: IsRadixKey k => k -> SelEq k STree
selEq = SelEqT . toRadixKey

-- I'm writing this for the forth time or something.
-- Me, please, DO NOT DELETE THIS.
data family SelNonDet k t -- access existing value by choosing

data instance SelNonDet k STree = SelNonDetT
data instance SelNonDet k SChunk = SelNonDetC

-- I don't agree with how it is, but True refers to the left option
-- and False refers to the right option of Choose.
-- Why? I don't know.
instance Has (AppIO :+: Reduce :+: NonDet) sig m => Selector SelNonDet m where
  selTree SelNonDetT valM = do
    now <- send Choose
    if now
      then do
        exists <- isJust <$> fetchC valM
        unless exists E.empty
        pure Nothing
      else pure $ Just SelNonDetC
  selBin self _ = do
    left <- send Choose
    pure $ Just (not left, self)
  selTip SelNonDetC _chunk = pure $ Just SelNonDetT
  selNil _ = E.empty

selNonDet :: SelNonDet k STree
selNonDet = SelNonDetT

runNonDetMin :: Monad m => NonDetC m a -> m (Maybe a)
runNonDetMin = runNonDet
  (\l r -> l >>= \case
    Nothing -> r
    l' -> pure l')
  (pure . Just)
  (pure Nothing)

reverseNonDet :: NonDetC m a -> NonDetC m a -- Mi amas FP per tuta mia koro.
reverseNonDet act = NonDetC \choose p n -> runNonDet (flip choose) p n act
{-# INLINE reverseNonDet #-}

runNonDetMax :: Monad m => NonDetC m a -> m (Maybe a)
runNonDetMax = runNonDetMin . reverseNonDet

-- For each value produced by the NonDetC m a, run the function.
-- The function returns whether to continue consuming the NonDet computation.
forNonDet_ :: Algebra sig m => NonDetC m a -> (a -> m Bool) -> m ()
forNonDet_ gen f = void $ runNonDetMin do
  i <- gen
  lift (f i) >>= \case
    True -> E.empty -- Mark branch as "failed" and move on to the next one.
    False -> pure () -- Mark branch as successful, finishing the NonDet.

data family SelEqNonDet k t

data instance SelEqNonDet k STree = SelEqNonDetT ![Chunk] | SelEqNonDetOffT
data instance SelEqNonDet k SChunk = SelEqNonDetC !Chunk ![Chunk] | SelEqNonDetOffC

selEqChoose :: IsRadixKey k => k -> SelEqNonDet k STree
selEqChoose k =
  let k' = toRadixKey k
  in SelEqNonDetT k'

-- range

data RBound f =
  RBUnrestricted -- Ord-predicate is known to be true on this subrange
  | RBRestricted { _inclusive :: Bool, _path :: f Chunk } -- Ord-predicate
type RangeT = (RBound [], RBound [])
type RangeC = (RBound NonEmpty, RBound NonEmpty)

-- 
restrictRBoundC :: (Chunk -> Chunk -> Bool) -> RBound NonEmpty -> Chunk -> Maybe (RBound NonEmpty)
restrictRBoundC _ RBUnrestricted _ = Just RBUnrestricted
restrictRBoundC cmp self@(RBRestricted _incl (p :| _ps)) mask = case tryMask mask p of
  -- TODO: tryMask is used to evaluate whether the key belongs to the subrange. Is this optimal?
  Nothing -> guard (p `cmp` mask) *> Just RBUnrestricted
  Just _ -> Just self

restrictRangeC :: Chunk -> RangeC -> Maybe RangeC
restrictRangeC mask (lbound, rbound) = (,)
  <$> restrictRBoundC (<) lbound mask
  <*> restrictRBoundC (>) rbound mask

unconsRBoundC :: (Chunk -> Chunk -> Bool) -> RBound NonEmpty -> Chunk -> Maybe (RBound [])
unconsRBoundC _ RBUnrestricted _ = Just RBUnrestricted
unconsRBoundC cmp (RBRestricted incl (p :| ps)) curr =
  if p `cmp` curr
    then Just $
      if p == curr
        then RBRestricted incl ps
        else RBUnrestricted
    else Nothing

unconsRangeC :: RangeC -> Chunk -> Maybe RangeT
unconsRangeC (lbound, rbound) chunk = (,)
  <$> unconsRBoundC (<=) lbound chunk
  <*> unconsRBoundC (>=) rbound chunk

unconsRangeT :: RangeT -> (Bool, Maybe RangeC)
unconsRangeT (lbound, rbound) =
  -- This code is very stupid, but I wanted to capture the logic precisely.
  let elWithinLeft = case lbound of
        RBUnrestricted -> True
        RBRestricted incl path -> (if incl then (<=) else (<)) path []
      elWithinRight = case rbound of
        RBUnrestricted -> True
        RBRestricted incl path -> (if incl then (<=) else (<)) [] path
      uncons' = \case
        RBUnrestricted -> Just RBUnrestricted
        RBRestricted incl (p:ps) -> Just $ RBRestricted incl (p :| ps)
        RBRestricted _incl [] -> Nothing
  in (elWithinLeft && elWithinRight, (,) <$> uncons' lbound <*> uncons' rbound)

data family SelNonDetRanged k t

newtype instance SelNonDetRanged k STree = SelNonDetRangedT RangeT
newtype instance SelNonDetRanged k SChunk = SelNonDetRangedC RangeC

instance Has (AppIO :+: Reduce :+: NonDet) sig m => Selector SelNonDetRanged m where
  selTree (SelNonDetRangedT range0) valM =
    let (this, rangeM) = unconsRangeT range0 in
    (do
      E.guard this
      E.guard . isJust =<< fetchC valM
      pure Nothing)
    <|> maybe E.empty (pure . Just . SelNonDetRangedC) rangeM
  selBin (SelNonDetRangedC range0) mask =
    maybe E.empty (\r -> Just . (, SelNonDetRangedC r) <$> (pure False <|> pure True)) $ restrictRangeC mask range0
  selTip (SelNonDetRangedC range0) key =
    maybe E.empty (pure . Just . SelNonDetRangedT) $ unconsRangeC range0 key
  selNil _ = E.empty

selNonDetRanged :: RangeT -> SelNonDetRanged k STree
selNonDetRanged = SelNonDetRangedT

-- construction

empty :: Container c => RadixTree c k a
empty = RadixTree (wrapB sNothing) (wrapB sNil)

fromListM :: forall c sig m k v. (Has AppIO sig m, Container c, IsRadixKey k, Typeable k, Ser v) => [(k, v)] -> m (RadixTree c k v)
fromListM = foldM (\t (k, v) -> insert (selEq k) v t) empty

toListM :: forall c sig m k v. (Has AppIO sig m, Container c, IsRadixKey k, Typeable k, Ser v) => RadixTree c k v -> m [(k, v)]
toListM = fmap catMaybes . runNonDetA . lookupKV selNonDet

toDelayed :: forall k v. (Typeable k, Ser v) => RadixTree Res k v -> RadixTree Delay k v
toDelayed (RadixTree valM subM) = RadixTree (DelayPin valM) (toDelayedC subM) where
  toDelayedC :: Res (RadixChunk Res k v) -> Delay (RadixChunk Delay k v)
  toDelayedC x = mkDelayLazy $ fetch x >>= (readReducible >>> \case
    Nil -> pure $ wrapB sNil
    Tip k rt -> allocC $ mkReducible $ Tip k $ toDelayed rt
    Bin k a b -> allocC $ mkReducible $ Bin k (toDelayedC a) (toDelayedC b))

-- debug

-- Stupid String-based show for debug
tryFetchShow :: (Container c, Show a) => c a -> String
tryFetchShow = maybe "<>" show . tryFetchC

-- instance (Container c, Show a) => Show (RadixTree c k a) where
--   show (RadixTree val chunk) = "(RadixTree (" <> tryFetchShow val <> ") " <> tryFetchShow chunk <> ")"
-- instance (Container c, Show a) => Show (RadixChunk' c k a) where
--   show = \case
--     Nil -> "Nil"
--     Tip key val -> "(Tip " <> show key <> " " <> show val <> ")"
--     Bin mask l r -> "(Bin " <> show mask <> " " <> tryFetchShow l <> " " <> tryFetchShow r <> ")"
