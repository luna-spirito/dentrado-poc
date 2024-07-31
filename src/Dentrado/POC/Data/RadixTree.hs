{-# LANGUAGE RecursiveDo, PatternSynonyms #-}
module Dentrado.POC.Data.RadixTree where
import RIO hiding (mask, toList, catch)
import Data.Bits
import Control.Algebra
import Control.Effect.Writer
import Dentrado.POC.Data.Container
import Control.Effect.Fresh (Fresh)
import Data.Foldable (foldrM)
import Dentrado.POC.TH (moduleId, sRunEvalFresh)
import Control.Carrier.Writer.Church (WriterC, runWriter)
import Control.Monad.Fix (MonadFix)
import Data.Monoid (First(..))

$(moduleId 1)

-- TODO: mkTip!!

type Chunk = Word32

tryMask :: Chunk -> Chunk -> Maybe Bool
tryMask mask key =
  if prefixBits .&. mask == prefixBits .&. key
  then Just $ 1 .&. (key `unsafeShiftR` countTrailingZeros mask) == 1
  else Nothing
  where
    prefixBits = complement $ mask - 1 `xor` mask

makeMask :: Chunk -> Chunk -> (Chunk, Bool)
makeMask l r =
  let maskBit = unsafeShiftL 1 (finiteBitSize (0 :: Chunk) - 1 - countLeadingZeros (l `xor` r))
  in (maskBit .|. (l .&. complement (maskBit-1)), r .&. maskBit /= 0)

-- task: better key support
-- build "key" marker into the RadixTree datatype, allow different keys to be used, implement min/max view.

class IsRadixKey key where
  toRadixKey :: key -> [Chunk]
  -- fromRadixKey :: [Chunk] -> key

instance IsRadixKey [Chunk] where
  toRadixKey = id

-- TODO: Implement Zebra simply by adding metadata field to Nil
-- Justification: RadixTree stores discrete and continuous data,
-- with discrete data being saved in Tip and continuous data being
-- saved in Nil. Typically the only continuous data that we work with
-- is "there's nothing here in this continuous region".
-- But this could be repurposed to store more cases.
data RadixTree c k a = RadixTree !(c (Maybe a)) !(c (RadixChunk c k a)) -- both element and next is containerized, both can be left unwrapped.
type RadixChunk c k a = Reducible (RadixChunk' c k a)
data RadixChunk' c k a
  = Nil
  | Tip !Chunk !(RadixTree c k a) -- RadixTree is the only possible branch. Still could be containerized, but I'm not sure it's worth it
  | Bin !Chunk !(c (RadixChunk c k a)) !(c (RadixChunk c k a)) -- Either branch can be accessed, so containerization

-- -- TODO: Don't know how effective is this
reduceChunk'' :: (Container c, Has (Writer (Reduced' s)) sig m) => Proxy s -> RadixChunk' c k a -> m (RadixChunk' c k a, Maybe (c (RadixChunk c k a)))
reduceChunk'' (Proxy @s) = \case
  Tip _ (RadixTree (tryFetchC -> Just Nothing) (tryFetchC -> Just (readReducible -> Nil))) -> tell (Reduced' @s True) $> (Nil, Just sNil)
  Bin _ left'@(tryFetchC -> Just (readReducible -> left)) right'@(tryFetchC -> Just (readReducible -> right))
    | Nil <- left -> tell (Reduced' @s True) $> (right, Just left') -- hopefully no need to reduceChunk left/right
    | Nil <- right -> tell (Reduced' @s True) $> (left, Just right')
  nonReducible -> pure (nonReducible, Nothing)
{-# INLINE reduceChunk'' #-}

reduceChunk' :: (Container c, Has (Writer (Reduced' s)) sig m) => Proxy s -> RadixChunk' c k a -> m (RadixChunk' c k a)
reduceChunk' p v = fst <$> reduceChunk'' p v
{-# INLINE reduceChunk' #-}

reduceChunk :: (Container c, Has (Writer Reduced) sig m) => RadixChunk' c k a -> m (RadixChunk' c k a)
reduceChunk x = reduceChunk' (Proxy @"") x
{-# INLINE reduceChunk #-}

allocReducedChunk :: (Container c1, Container c2, Has Fresh sig m) => (forall b. c2 b -> WriterC Reduced m (c1 b)) -> RadixChunk' c2 k a -> m (c1 (RadixChunk c2 k a))
allocReducedChunk f c = nonRe $ reduceChunk'' (Proxy @"") c >>= \case
  (v, Nothing) -> allocC $ mkReducible v
  (_, Just v) -> f v
{-# INLINE allocReducedChunk #-}

-- -- Let's make accessRadix and accessRadix1?
accessRadix1 :: forall c k a tree chunk sig m. (Container c, Has (Fresh :+: Writer Reduced) sig m)
  => (c (Maybe a) -> chunk -> tree) -- ^ on sub, tree
  -> (RadixTree c k a -> tree) -- ^ on found, tree
  -> (Chunk -> [Chunk] -> chunk) -- ^ on missing, chunk
  -> (Chunk -> tree -> chunk) -- ^ on Tip, chunk
  -> (Bool -> Chunk -> c (RadixChunk c k a) -> chunk -> chunk) -- ^ on branch, chunk
  -> Chunk
  -> [Chunk]
  -> c (RadixChunk c k a)
  -> m chunk
accessRadix1 onSubT onFoundT onMissingC onTipC onBranchC =
  let
    goChunk :: Chunk -> [Chunk] -> c (RadixChunk c k a) -> m chunk
    goChunk key keys chunkM =
      let
        newBranch :: Chunk -> chunk
        newBranch exKey =
          let (mask, placeRight) = makeMask exKey key
          in onBranchC placeRight mask chunkM $ onMissingC key keys
      in fetchC chunkM >>= \chunk -> reducible reduceChunk chunk \case
        Nil -> pure $ onMissingC key keys
        (Tip key2 subtree)
          | key == key2 -> onTipC key <$> goTree keys subtree
          | otherwise -> pure $ newBranch key2
        (Bin mask l r)
          | Just pickRight <- tryMask mask key
            -> onBranchC pickRight mask (if pickRight then l else r) <$> goChunk key keys (if pickRight then r else l)
          | otherwise -> pure $ newBranch mask
    goTree :: [Chunk] -> RadixTree c k a -> m tree
    goTree [] = pure . onFoundT
    goTree (key:keys) = \(RadixTree val chunk) -> onSubT val <$> goChunk key keys chunk
  in goChunk
{-# INLINE accessRadix1 #-}

-- TODO: use same m everywhere
-- Constructs both accessRadix1 and accessRadix versions
accessRadix :: forall c k a tree chunk sig m. (Container c, Has (Fresh :+: Writer Reduced) sig m)
  => (c (Maybe a) -> chunk -> tree) -- ^ on sub, tree
  -> (RadixTree c k a -> tree) -- ^ on found, tree
  -> (Chunk -> [Chunk] -> chunk) -- ^ on missing, chunk
  -> (Chunk -> tree -> chunk) -- ^ on Tip, chunk
  -> (Bool -> Chunk -> c (RadixChunk c k a) -> chunk -> chunk) -- ^ on branch, chunk
  -> (Chunk -> [Chunk] -> c (RadixChunk c k a) -> m chunk, [Chunk] -> RadixTree c k a -> m tree)
accessRadix onSubT onFoundT onMissingC onTipC onBranchC =
  let
    var1 :: Chunk -> [Chunk] -> c (RadixChunk c k a) -> m chunk
    var1 = accessRadix1 onSubT onFoundT onMissingC onTipC onBranchC
  in (var1, \case
    [] -> pure . onFoundT
    (key:keys) -> \(RadixTree val chunk) -> onSubT val <$> var1 key keys chunk
  )
{-# INLINE accessRadix #-}

mkBinNonRe :: Container c => Bool -> Chunk -> c (RadixChunk c k a) -> c (RadixChunk c k a) -> RadixChunk' c k a
mkBinNonRe right mask a b = Bin mask (if right then a else b) (if right then b else a)
{-# INLINE mkBinNonRe #-}

mkBin :: (Container c1, Container c2, Has Fresh sig m)  => (forall b. c2 b -> WriterC Reduced m (c1 b)) -> Bool -> Chunk -> c2 (RadixChunk c2 k a) -> c2 (RadixChunk c2 k a) -> m (c1 (RadixChunk c2 k a))
mkBin f a b c d = allocReducedChunk f $ mkBinNonRe a b c d
{-# INLINE mkBin #-}

mkTipNonRe :: Chunk -> RadixTree c k a -> RadixChunk' c k a
mkTipNonRe = Tip

mkTip :: (Container c1, Container c2, Has Fresh sig m) => (forall b. c2 b -> WriterC Reduced m (c1 b)) -> Chunk -> RadixTree c2 k a -> m (c1 (RadixChunk c2 k a))
mkTip f k v = allocReducedChunk f $ mkTipNonRe k v
{-# INLINE mkTip #-}

internalLookup :: (Container c, Has (Fresh :+: Writer Reduced) sig m) => (Chunk -> [Chunk] -> c (RadixChunk c k a) -> m (m (Maybe a)), [Chunk] -> RadixTree c k a -> m (m (Maybe a)))
internalLookup = accessRadix
  (\_ -> id)
  (\(RadixTree a _) -> fetchC a)
  (\_ _ -> pure Nothing)
  (\_ -> id)
  (\_ _ _ -> id)
{-# INLINE internalLookup #-}

lookup :: Has Fresh sig m => Container c => [Chunk] -> RadixTree c k a -> m (Maybe a)
lookup k tr = nonRe $ join $ snd internalLookup k tr

sNil :: Container c => c (RadixChunk c k a)
sNil = $sRunEvalFresh $ allocC $ mkReducible Nil

internalInsert :: forall c k sig m a. (Container c, Has (Fresh :+: Writer Reduced) sig m) => a -> (Chunk -> [Chunk] -> c (RadixChunk c k a) -> m (m (c (RadixChunk c k a))), [Chunk] -> RadixTree c k a -> m (m (RadixTree c k a)))
internalInsert val = accessRadix
  (\a b -> RadixTree a <$> b)
  (\(RadixTree _oldVal b) -> (`RadixTree` b) <$> allocC (Just val))
  (\key1 keys2 -> do
    finalVal <- allocC $ Just val
    (_state, res) <- foldrM
      (\key (subval, subchunk) ->
        (sNothing,) <$> allocC (mkReducible $ mkTipNonRe key $ RadixTree subval subchunk)) -- unlikely reduced
      (finalVal, sNil)
      (key1:keys2)
    pure res)
  (\k v -> allocC . mkReducible . mkTipNonRe k =<< v)
  (\k r a b -> allocC . mkReducible . mkBinNonRe k r a =<< b)
{-# INLINE internalInsert #-}

-- short-circuit
insert :: (Container c, Has Fresh sig m) => [Chunk] -> p -> RadixTree c k p -> m (RadixTree c k p)
insert k v tr = nonRe $ join $ snd (internalInsert v) k tr

-- internalDelete :: (Container c, Has (Fresh :+: Writer Reduced) sig m) => (Chunk -> [Chunk] -> c (RadixChunk c k a) -> m (m (c (RadixChunk c k a))), [Chunk] -> RadixTree c k a -> m (m (RadixTree c k a)))
-- internalDelete = accessRadix
--   (\a b -> RadixTree a <$> b) -- on sub, tree
--   (\(RadixTree _deleted sub) -> pure $ RadixTree sNothing sub) -- on found, tree
--   (\_key1 _keys2 -> pure sNil) -- on missing, chunk
--   (\key tree -> mkTip pure key =<< tree) -- on Tip, chunk
--   (\k r a b -> mkBin pure k r a =<< b) -- on branch, chunk
-- {-# INLINE internalDelete #-}

-- delete :: (Container c, Has Fresh sig m) => [Chunk] -> RadixTree c k p -> m (RadixTree c k p)
-- delete k tr = nonRe $ join $ snd internalDelete k tr

-- could be m (f (...)), but I don't think it's worth it
internalUpdate :: (Container c, Has (Fresh :+: Writer Reduced) sig m)
  => (c (Maybe a) -> m (c (Maybe a))) -> (Chunk -> [Chunk] -> c (RadixChunk c k a) -> m (m (c (RadixChunk c k a))), [Chunk] -> RadixTree c k a -> m (m (RadixTree c k a)))
internalUpdate f = accessRadix
  (\a b -> RadixTree a <$> b) -- on sub, tree
  (\(RadixTree updated sub) -> (`RadixTree` sub) <$> f updated) -- on found, tree
  (\_key1 _keys2 -> pure sNil) -- on missing, chunk
  (\key tree -> mkTip pure key =<< tree) -- on Tip, chunk
  (\k r a b -> mkBin pure k r a =<< b) -- on branch, chunk
{-# INLINE internalUpdate #-}

-- short-circuit?
update :: (Container c, Has Fresh sig m) => (c (Maybe a) -> WriterC Reduced m (c (Maybe a))) -> [Chunk] -> RadixTree c k a -> m (RadixTree c k a)
update f k tr = nonRe $ join $ snd (internalUpdate f) k tr

-- short-circuit
delete :: (Container c, Has Fresh sig m) => [Chunk] -> RadixTree c k a -> m (RadixTree c k a)
delete = update (\_ -> pure sNothing)

pop :: (Container c, Has Fresh sig m) => [Chunk] -> RadixTree c k a -> m (Maybe a, RadixTree c k a)
pop k rt = runWriter (\(First a) b -> pure (a, b)) $ update
  (\v -> do
    v' <- fetchC v
    tell $ First v'
    pure sNothing
  )
  k rt

empty :: Container c => RadixTree c k a
empty = RadixTree sNothing sNil

sEmpty :: Container c => c (RadixTree c k a)
sEmpty = $sRunEvalFresh $ allocC empty

-- TODO: monadical extract, separate RadixTree and RadixZipper into different modules, `merge`, `adjust`

data OnOne c other fin = OnOne
  { onOneVal :: !(Res (Maybe other) -> other -> FreshM (Res (Maybe fin))) -- other must be unwrapped for this conclusion
  , onOneSubtree :: !(forall k. Res (RadixChunk c k other) -> FreshM (Res (RadixChunk c k fin))) }
newtype OnBoth one two fin = OnBoth
  { onBothVal :: Res (Maybe one) -> one -> Res (Maybe two) -> two -> FreshM (Res (Maybe fin)) }
newtype MergeStrategy c = MergeStrategy
  { _apply :: forall x y z. Res (Res x -> Res y -> WriterC (Reduced' "1") (WriterC (Reduced' "2") FreshM) (Res z)) -> c x -> c y -> WriterC (Reduced' "1") (WriterC (Reduced' "2") FreshM) (c z) }

merge :: forall one two fin c k. forall sig1 m1. (Container c, Has Fresh sig1 m1, MonadFix m1)
  => MergeStrategy c
  -> OnOne c one fin
  -> OnOne c two fin
  -> OnBoth one two fin
  -> m1 (RadixTree c k one
    -> RadixTree c k two
    -> FreshM (RadixTree c k fin))
merge (MergeStrategy apply) one1 one2 both = mdo
  mergeVal <- alloc \r1 r2 -> do
    v1 <- fetch r1
    v2 <- fetch r2
    lift $ lift $ case (v1, v2) of
      (Just a , Just b ) -> onBothVal both r1 a r2 b
      (Just a , Nothing) -> onOneVal one1 r1 a
      (Nothing, Just b ) -> onOneVal one2 r2 b
      (Nothing, Nothing) -> pure sNothing
  let unsafeMask = \case
        Nil -> error "impossible"
        Tip mask _ -> mask
        Bin mask _ _ -> mask
  mergeChunk <- alloc \res1 res2 -> do
    v1 <- fetch res1
    v2 <- fetch res2
    reducible' (Proxy @"1") (reduceChunk' (Proxy @"1")) v1 \v1' ->
      reducible' (Proxy @"2") (reduceChunk' (Proxy @"2")) v2 \v2' ->
        case (v1', v2') of
          (_, Nil) -> lift $ lift $ onOneSubtree one1 res1
          (Nil, _) -> lift $ lift $ onOneSubtree one2 res2
          (Bin mask1 l1 r1, Bin mask2 l2 r2)
            | mask1 == mask2 -> do
              a <- apply mergeChunk l1 l2
              b <- apply mergeChunk r1 r2
              mkBin unwrap True mask1 a b
          (Bin mask1 l1 r1, unsafeMask -> mask2)
            | Just pickRight <- tryMask mask1 mask2
              -> if pickRight
                  then do
                    a <- apply mergeChunk l1 sNil
                    b <- apply mergeChunk r1 (wrap res2)
                    mkBin unwrap True mask1 a b
                  else do
                    a <- apply mergeChunk l1 (wrap res2)
                    b <- apply mergeChunk r1 sNil
                    mkBin unwrap True mask1 a b
          (unsafeMask -> mask1, Bin mask2 l2 r2)
            | Just pickRight <- tryMask mask2 mask1
              -> if pickRight
                  then do
                    a <- apply mergeChunk sNil l2
                    b <- apply mergeChunk (wrap res1) r2
                    mkBin unwrap True mask1 a b
                  else do
                    a <- apply mergeChunk (wrap res1) l2
                    b <- apply mergeChunk sNil r2
                    mkBin unwrap True mask1 a b
          (Tip mask1 l, Tip mask2 r)
            | mask1 == mask2 -> mkTip unwrap mask1 =<< mergeTree l r
          (unsafeMask -> mask1, unsafeMask -> mask2) -> do
            let (mask, pickRight) = makeMask mask1 mask2
            a <- lift $ lift $ onOneSubtree one1 res1
            b <- lift $ lift $ onOneSubtree one2 res2
            mkBin unwrap pickRight mask (wrap a) (wrap b)
  let mergeTree (RadixTree k1 s1) (RadixTree k2 s2) =
        RadixTree
          <$> apply mergeVal k1 k2
          <*> apply mergeChunk s1 s2
  pure \a b -> nonRe' @"2" $ nonRe' @"1" $ mergeTree a b


-- merge = runWriter @(Reduced' "one") (\_ -> pure) $ runWriter @(Reduced' "two") (\_ -> pure) $ getCompose $ mergeTree [] a b where
--   merger = _
--   mergeTree p (RadixTree v1 s1) (RadixTree v2 s2) = _
-- valid, but non-streaming
-- merge :: forall f c one two fin. (Applicative f, Container c)
--   => OnOne f one fin
--   -> OnOne f two fin
--   -> OnBoth f one two fin
--   -> RadixTree c k one
--   -> RadixTree c k two
--   -> f (RadixTree c k fin)
-- merge one1 one2 match = \a b -> runIdentity $ runWriter @(Reduced' "one") (\_ -> pure) $ runWriter @(Reduced' "two") (\_ -> pure) $ getCompose $ mergeTree [] a b where
--   mergeVal p v1M v2M = Compose do
--     v1 <- extract' (Proxy @"one") v1M
--     v2 <- extract' (Proxy @"two") v2M
--     pure case (v1, v2) of
--       (Just a , Just b ) -> onBothVal match p a b
--       (Just a , Nothing) -> onOneVal one1 p a
--       (Nothing, Just b ) -> onOneVal one2 p b
--       (Nothing, Nothing) -> pure Nothing
--   mergeTree p (RadixTree v1 s1) (RadixTree v2 s2) = RadixTree <$> (construct <$> mergeVal p v1 v2) <*> mergeChunk p s1 s2
--   mergeChunk p s1RM s2RM = Compose do
--     s1R <- extract' (Proxy @"one") s1RM
--     s2R <- extract' (Proxy @"two") s2RM
--     reducible' (Proxy @"one") (reduceChunk' (Proxy @"one")) s1R \s1 ->
--       reducible' (Proxy @"two") (reduceChunk' (Proxy @"two")) s2R \s2 ->
        -- _
-- mergeVal = construct \p v1 v2 -> case (v1, v2) of
--   (Just a , Just b ) -> runIdentity $ onBothVal both p a b
--   (Just a , Nothing) -> runIdentity $ onOneVal one1 p a
--   (Nothing, Just b ) -> runIdentity $ onOneVal one2 p b
--   (Nothing, Nothing) -> Nothing

-- sMerge :: Container c
--   => OnOne Identity one fin
--   -> OnOne Identity two fin
--   -> OnBoth Identity one two fin
--   -> RadixTree c k one
--   -> RadixTree c k two
--   -> RadixTree c k fin
-- sMerge one1 one2 both = mergeTree [] where
--   mergeTree p (RadixTree v1 s1) (RadixTree v2 s2) = RadixTree (mergeVal <*> p <*> v1 <*> v2) _

-- TODO: monadic... monadic


-- debug

-- Stupid String-based show for debug
tryFetchShow :: (Container c, Show a) => c a -> String
tryFetchShow = maybe "<>" show . tryFetchC

instance (Container c, Show a) => Show (RadixTree c k a) where
  show (RadixTree val chunk) = "(RadixTree (" <> tryFetchShow val <> ") " <> tryFetchShow chunk <> ")"
instance (Container c, Show a) => Show (RadixChunk' c k a) where
  show = \case
    Nil -> "Nil"
    Tip key val -> "(Tip " <> show key <> " " <> show val <> ")"
    Bin mask l r -> "(Bin " <> show mask <> " " <> tryFetchShow l <> " " <> tryFetchShow r <> ")"
