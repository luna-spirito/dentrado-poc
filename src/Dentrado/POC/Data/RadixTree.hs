{-# LANGUAGE RecursiveDo #-}
module Dentrado.POC.Data.RadixTree where
import RIO hiding (mask, toList, catch)
import Data.Bits
import Control.Algebra
import Control.Effect.Writer
import Dentrado.POC.Data.Container
import Control.Effect.Fresh (Fresh)
import Data.Foldable (foldrM)
import Dentrado.POC.TH (moduleId, sRunEvalFresh)
import Control.Carrier.Writer.Church (WriterC)
import Control.Monad.Fix (MonadFix)

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

-- TODO: Implement Zebra simply by adding metadata field to Nil
-- Justification: RadixTree stores discrete and continuous data,
-- with discrete data being saved in Tip and continuous data being
-- saved in Nil. Typically the only continuous data that we work with
-- is "there's nothing here in this continuous region".
-- But this could be repurposed to store more cases.
data RadixTree c a = RadixTree !(c (Maybe a)) !(c (RadixChunk c a)) -- both element and next is containerized, both can be left unwrapped.
type RadixChunk c a = Reducible (RadixChunk' c a)
data RadixChunk' c a
  = Nil
  | Tip !Chunk !(RadixTree c a) -- RadixTree is the only possible branch. Still could be containerized, but I'm not sure it's worth it
  | Bin !Chunk !(c (RadixChunk c a)) !(c (RadixChunk c a)) -- Either branch can be accessed, so containerization

-- -- TODO: Don't know how effective is this
reduceChunk' :: (Container c, Has (Writer (Reduced' s)) sig m) => Proxy s -> RadixChunk' c a -> m (RadixChunk' c a)
reduceChunk' (Proxy @s) = \case
  Tip _ (RadixTree (tryExtract -> Just Nothing) (tryExtract -> Just (readReducible -> Nil))) -> tell (Reduced' @s True) $> Nil
  Bin _ (tryExtract -> Just (readReducible -> left)) (tryExtract -> Just (readReducible -> right))
    | Nil <- left -> tell (Reduced' @s True) $> right -- hopefully no need to reduceChunk left/right
    | Nil <- right -> tell (Reduced' @s True) $> left
  nonReducible -> pure nonReducible

reduceChunk :: (Container c, Has (Writer Reduced) sig m) => RadixChunk' c a -> m (RadixChunk' c a)
reduceChunk = reduceChunk' (Proxy @"")

-- -- Let's make accessRadix and accessRadix1?
accessRadix1 :: forall c a tree chunk sig m. (Container c, Has (Fresh :+: Writer Reduced) sig m)
  => (c (Maybe a) -> chunk -> tree) -- ^ on sub, tree
  -> (RadixTree c a -> tree) -- ^ on found, tree
  -> (Chunk -> [Chunk] -> chunk) -- ^ on missing, chunk
  -> (Chunk -> tree -> chunk) -- ^ on Tip, chunk
  -> (Bool -> Chunk -> c (RadixChunk c a) -> chunk -> chunk) -- ^ on branch, chunk
  -> Chunk
  -> [Chunk]
  -> c (RadixChunk c a)
  -> m chunk
accessRadix1 onSubT onFoundT onMissingC onTipC onBranchC =
  let
    goChunk :: Chunk -> [Chunk] -> c (RadixChunk c a) -> m chunk
    goChunk key keys chunkM =
      let
        newBranch :: Chunk -> chunk
        newBranch exKey =
          let (mask, placeRight) = makeMask exKey key
          in onBranchC placeRight mask chunkM $ onMissingC key keys
      in extract chunkM >>= \chunk -> reducible reduceChunk chunk \case
        Nil -> pure $ onMissingC key keys
        (Tip key2 subtree)
          | key == key2 -> onTipC key <$> goTree keys subtree
          | otherwise -> pure $ newBranch key2
        (Bin mask l r)
          | Just pickRight <- tryMask mask key
            -> onBranchC pickRight mask (if pickRight then l else r) <$> goChunk key keys (if pickRight then r else l)
          | otherwise -> pure $ newBranch mask
    goTree :: [Chunk] -> RadixTree c a -> m tree
    goTree [] = pure . onFoundT
    goTree (key:keys) = \(RadixTree val chunk) -> onSubT val <$> goChunk key keys chunk
  in goChunk
{-# INLINE accessRadix1 #-}

-- TODO: use same m everywhere
-- Constructs both accessRadix1 and accessRadix versions
accessRadix :: forall c a tree chunk sig m. (Container c, Has (Fresh :+: Writer Reduced) sig m)
  => (c (Maybe a) -> chunk -> tree) -- ^ on sub, tree
  -> (RadixTree c a -> tree) -- ^ on found, tree
  -> (Chunk -> [Chunk] -> chunk) -- ^ on missing, chunk
  -> (Chunk -> tree -> chunk) -- ^ on Tip, chunk
  -> (Bool -> Chunk -> c (RadixChunk c a) -> chunk -> chunk) -- ^ on branch, chunk
  -> (Chunk -> [Chunk] -> c (RadixChunk c a) -> m chunk, [Chunk] -> RadixTree c a -> m tree)
accessRadix onSubT onFoundT onMissingC onTipC onBranchC =
  let
    var1 :: Chunk -> [Chunk] -> c (RadixChunk c a) -> m chunk
    var1 = accessRadix1 onSubT onFoundT onMissingC onTipC onBranchC
  in (var1, \case
    [] -> pure . onFoundT
    (key:keys) -> \(RadixTree val chunk) -> onSubT val <$> var1 key keys chunk
  )
{-# INLINE accessRadix #-}

mkBinNonRe :: Container c => Bool -> Chunk -> c (RadixChunk c a) -> c (RadixChunk c a) -> RadixChunk' c a
mkBinNonRe right mask a b = Bin mask (if right then a else b) (if right then b else a)
{-# INLINE mkBinNonRe #-}

mkBin :: (Container c, Algebra sig m)  => Bool -> Chunk -> c (RadixChunk c a) -> c (RadixChunk c a) -> m (RadixChunk' c a)
mkBin a b c d = nonRe $ reduceChunk $ mkBinNonRe a b c d
{-# INLINE mkBin #-}

mkTipNonRe :: Chunk -> RadixTree c a -> RadixChunk' c a
mkTipNonRe = Tip

mkTip :: (Container c, Algebra sig m) => Chunk -> RadixTree c a -> m (RadixChunk' c a)
mkTip k v = nonRe $ reduceChunk $ mkTipNonRe k v
{-# INLINE mkTip #-}

internalLookup :: (Container c, Has (Fresh :+: Writer Reduced) sig m) => (Chunk -> [Chunk] -> c (RadixChunk c a) -> m (m (Maybe a)), [Chunk] -> RadixTree c a -> m (m (Maybe a)))
internalLookup = accessRadix
  (\_ -> id)
  (\(RadixTree a _) -> extract a)
  (\_ _ -> pure Nothing)
  (\_ -> id)
  (\_ _ _ -> id)
{-# INLINE internalLookup #-}

lookup :: Has Fresh sig m => Container c => [Chunk] -> RadixTree c a -> m (Maybe a)
lookup k tr = nonRe $ join $ snd internalLookup k tr

sNil :: Container c => c (RadixChunk c a)
sNil = $sRunEvalFresh $ construct $ mkReducible Nil

internalInsert :: forall c sig m a. (Container c, Has (Fresh :+: Writer Reduced) sig m) => a -> (Chunk -> [Chunk] -> c (RadixChunk c a) -> m (m (c (RadixChunk c a))), [Chunk] -> RadixTree c a -> m (m (RadixTree c a)))
internalInsert val = accessRadix
  (\a b -> RadixTree a <$> b)
  (\(RadixTree _oldVal b) -> (`RadixTree` b) <$> construct (Just val))
  (\key1 keys2 -> do
    finalVal <- construct $ Just val
    (_state, res) <- foldrM
      (\key (subval, subchunk) ->
        (sNothing,) <$> construct (mkReducible $ mkTipNonRe key $ RadixTree subval subchunk)) -- unlikely reduced
      (finalVal, sNil)
      (key1:keys2)
    pure res)
  (\k v -> construct . mkReducible . mkTipNonRe k =<< v)
  (\k r a b -> construct . mkReducible . mkBinNonRe k r a =<< b)
{-# INLINE internalInsert #-}

-- short-circuit
insert :: (Container c, Has Fresh sig m) => [Chunk] -> p -> RadixTree c p -> m (RadixTree c p)
insert k v tr = nonRe $ join $ snd (internalInsert v) k tr

internalDelete :: (Container c, Has (Fresh :+: Writer Reduced) sig m) => (Chunk -> [Chunk] -> c (RadixChunk c a) -> m (m (c (RadixChunk c a))), [Chunk] -> RadixTree c a -> m (m (RadixTree c a)))
internalDelete = accessRadix
  (\a b -> RadixTree a <$> b) -- on sub, tree
  (\(RadixTree _deleted sub) -> pure $ RadixTree sNothing sub) -- on found, tree
  (\_key1 _keys2 -> pure sNil) -- on missing, chunk
  (\key tree -> construct . mkReducible =<< mkTip key =<< tree) -- on Tip, chunk
  (\k r a b -> construct . mkReducible =<< mkBin k r a =<< b) -- on branch, chunk
{-# INLINE internalDelete #-}

-- short-circuit
delete :: (Container c, Has Fresh sig m) => [Chunk] -> RadixTree c p -> m (RadixTree c p)
delete k tr = nonRe $ join $ snd internalDelete k tr

empty :: Container c => RadixTree c a
empty = RadixTree sNothing sNil

sEmpty :: Container c => c (RadixTree c a)
sEmpty = $sRunEvalFresh $ construct empty

-- TODO: monadical extract, separate RadixTree and RadixZipper into different modules, `merge`, `adjust`

data OnOne other fin = OnOne
  { onOneVal :: !(other -> Maybe fin) -- other must be unwrapped for this conclusion
  , onOneSubtree :: !(forall c. Container c => RadixChunk' c other -> RadixChunk' c fin) }
newtype OnBoth one two fin = OnBoth
  { onBothVal :: one -> two -> Maybe fin }
newtype MergeStrategy c = MergeStrategy
  { _apply :: forall x y z. DPtr (Extracted c x -> Extracted c y -> WriterC (Reduced' "1") (WriterC (Reduced' "2") FreshM) z) -> c x -> c y -> WriterC (Reduced' "1") (WriterC (Reduced' "2") FreshM) (c z) }

merge :: forall one two fin c. forall sig1 m1. (Container c, Has Fresh sig1 m1, MonadFix m1)
  => MergeStrategy c
  -> OnOne one fin
  -> OnOne two fin
  -> OnBoth one two fin
  -> m1 (RadixTree c one
    -> RadixTree c two
    -> FreshM (RadixTree c fin))
merge {-(MergeStrategy doMerge)-} (MergeStrategy apply) one1 one2 both = mdo
  mergeVal <- construct \(Extracted _ val1) (Extracted _ val2) ->
    pure $ case (val1, val2) of
      (Just a , Just b ) -> onBothVal both a b
      (Just a , Nothing) -> onOneVal one1 a
      (Nothing, Just b ) -> onOneVal one2 b
      (Nothing, Nothing) -> Nothing
  let unsafeMask = \case
        Nil -> error "impossible"
        Tip mask _ -> mask
        Bin mask _ _ -> mask
  mergeChunk <- construct \(Extracted c1 c1v) (Extracted c2 c2v) ->
    reducible' (Proxy @"1") (reduceChunk' (Proxy @"1")) c1v \c1' ->
      reducible' (Proxy @"2") (reduceChunk' (Proxy @"2")) c2v \c2' ->
        mkReducible <$> case (c1', c2') of
          (a, Nil) -> pure $ onOneSubtree one1 a 
          (Nil, b) -> pure $ onOneSubtree one2 b
          (Bin mask1 l1 r1, Bin mask2 l2 r2)
            | mask1 == mask2 -> do
              a <- apply mergeChunk l1 l2
              b <- apply mergeChunk r1 r2
              mkBin True mask1 a b
          (Bin mask1 l1 r1, unsafeMask -> mask2)
            | Just pickRight <- tryMask mask1 mask2
              -> if pickRight
                  then do
                    a <- apply mergeChunk l1 sNil
                    b <- apply mergeChunk r1 c2 -- TODO: WRONG, COULD CAUSE DOUBLE EXTRACTION!!!
                    mkBin True mask1 a b
                  else do
                    a <- apply mergeChunk l1 c2
                    b <- apply mergeChunk r1 sNil
                    mkBin True mask1 a b
          (unsafeMask -> mask1, Bin mask2 l2 r2)
            | Just pickRight <- tryMask mask2 mask1
              -> if pickRight
                  then do
                    a <- apply mergeChunk sNil l2
                    b <- apply mergeChunk c1 r2
                    mkBin True mask1 a b
                  else do
                    a <- apply mergeChunk c1 l2
                    b <- apply mergeChunk sNil r2
                    mkBin True mask1 a b
          (Tip mask1 v1, Tip mask2 v2)
            | mask1 == mask2 -> Tip mask1 <$> mergeTree v1 v2
          (unsafeMask -> mask1, unsafeMask -> mask2) -> do
            let (mask, pickRight) = makeMask mask1 mask2
            a <- apply mergeChunk c1 sNil
            b <- apply mergeChunk sNil c2
            mkBin pickRight mask a b
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
--   -> RadixTree c one
--   -> RadixTree c two
--   -> f (RadixTree c fin)
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
--   -> RadixTree c one
--   -> RadixTree c two
--   -> RadixTree c fin
-- sMerge one1 one2 both = mergeTree [] where
--   mergeTree p (RadixTree v1 s1) (RadixTree v2 s2) = RadixTree (mergeVal <*> p <*> v1 <*> v2) _

-- TODO: monadic... monadic


-- debug

-- Stupid String-based show for debug
tryExtractShow :: (Container c, Show a) => c a -> String
tryExtractShow = maybe "<>" show . tryExtract

instance (Container c, Show a) => Show (RadixTree c a) where
  show (RadixTree val chunk) = "(RadixTree (" <> tryExtractShow val <> ") " <> tryExtractShow chunk <> ")"
instance (Container c, Show a) => Show (RadixChunk' c a) where
  show = \case
    Nil -> "Nil"
    Tip key val -> "(Tip " <> show key <> " " <> show val <> ")"
    Bin mask l r -> "(Bin " <> show mask <> " " <> tryExtractShow l <> " " <> tryExtractShow r <> ")"
