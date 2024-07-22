{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
module Dentrado.POC.Data where
import RIO hiding (mask, toList, catch)
import System.IO.Unsafe (unsafePerformIO)
import System.Mem.StableName (StableName, makeStableName, eqStableName)
import Control.Carrier.Empty.Church (runEmpty)
import Control.Effect.Empty (empty)
import Data.Typeable (eqT, type (:~:) (..))
import Data.Bits
import Control.Algebra
import Control.Carrier.Writer.Church (runWriter, WriterC)
import Data.Monoid (Any(..))
import Control.Effect.Writer
import GHC.Exts (IsList(..))

-- newtype BackList a = UnsafeBackList [a] deriving Eq

-- instance IsList (BackList a) where
--   type Item (BackList a) = a
--   fromList = UnsafeBackList . reverse
--   {-# INLINE fromList #-}
--   toList (UnsafeBackList l) = reverse l
--   {-# INLINE toList #-}

-- instance Semigroup (BackList a) where
--   (UnsafeBackList a) <> (UnsafeBackList b) = UnsafeBackList (b <> a)
--   {-# INLINE (<>) #-}

-- instance Monoid (BackList a) where
--   mempty = []
--   {-# INLINE mempty #-}

stableNameFor :: a -> StableName a
stableNameFor !x = unsafePerformIO $ makeStableName x

data Delay a where
  DelayAp :: Typeable a => !(Delay (a -> b)) -> !(Delay a) -> !(IORef (Maybe b)) -> Delay b
  DelayPin :: !a -> Delay a

dPure :: a -> Delay a
dPure = DelayPin

dAp :: Typeable a => Delay (a -> b) -> Delay a -> Delay b
dAp a b = DelayAp a b $ unsafePerformIO $ newIORef Nothing

-- | `Contains t` means that:
-- 1) It's possible to construct `t a` from `a`
-- 2) It's possible to `extract` `a` from `t a`
-- 3) It's possible to quickly check if two containers hold the same value,
-- but false negatives are possible
class Container t where
  construct :: a -> t a -- probably `a -> m (t a)`
  extract :: Has (Writer Any) sig m => t a -> m a -- probably `t a -> m a`
  tryExtract :: t a -> Maybe a
  same :: t a -> t b -> Bool

instance Container Identity where
  construct = Identity
  extract = pure . runIdentity
  tryExtract = Just . runIdentity
  same a b = stableNameFor (runIdentity a) `eqStableName` stableNameFor (runIdentity b)

instance Container Delay where
  construct = dPure
  extract = \case
    DelayPin x -> pure x
    DelayAp df da mv -> unsafePerformIO do
      vM <- readIORef mv
      case vM of
        Just v -> pure $ pure v
        Nothing -> do
          let v = run $ runWriter @Any (\_ y -> pure y) $ extract df <*> extract da
          writeIORef mv $ Just v
          pure $ tell (Any True) $> v
  tryExtract = \case
    DelayPin x -> Just x
    DelayAp _ _ mv -> unsafePerformIO $ readIORef mv
  same a b = case (a, b) of
    (DelayPin a', DelayPin b') -> stableNameFor a' `eqStableName` stableNameFor b'
    (DelayAp @a1 df1 da1 mv1, DelayAp @a2 df2 da2 mv2) ->
      unsafePerformIO (runEmpty (pure False) pure do
        v1 <- maybe empty pure =<< readIORef mv1
        v2 <- maybe empty pure =<< readIORef mv2
        pure $ stableNameFor v1 `eqStableName` stableNameFor v2)
      || maybe False (\Refl -> df1 `same` df2 && da1 `same` da2) (eqT @a1 @a2)
    (DelayAp {}, DelayPin _) -> False
    (DelayPin _, DelayAp {}) -> False

-- | Presence of Delay fields in some types interferes with construction of the most optimal spine.
-- Reducible is a potential fix that allows to "reduce" the spine as more Delayed computations
-- are resolved.
newtype Reducible a = Reducible (IORef a)

instance Show a => Show (Reducible a) where
  show = show . readReducible

mkReducible :: a -> Reducible a
mkReducible = Reducible . unsafePerformIO . newIORef

readReducible :: Reducible a -> a
readReducible (Reducible x) = unsafePerformIO $ readIORef x

catch :: forall w a sig m. (Monoid w, Has (Writer w) sig m) => m a -> m (w, a)
catch x = censor @w (const mempty) $ listen x

reducible :: Has (Writer Any) sig m => (a -> m a) -> Reducible a -> (a -> m b) -> m b
reducible reductor (Reducible red) f =
  let originalValue = unsafePerformIO $ readIORef red
  in do
    (Any changed, result) <- catch $ f originalValue
    if changed
      then do
        newValue <- reductor originalValue
        pure $ unsafePerformIO (writeIORef red newValue) `seq` result
      else
        pure result
{-# INLINE reducible #-}

-- Perform operation that can't really cause reduction of anything
nonRe :: WriterC Any Identity a -> a
nonRe = runIdentity . runWriter (\_ -> pure)

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
  | Tip !Chunk !(RadixTree c a) -- There's no way you access Tip and don't want to know what's coming next, so no containerization
  | Bin !Chunk !(c (RadixChunk c a)) !(c (RadixChunk c a)) -- Either branch can be accessed, so containerization

data InvRadixTree c a
  = InvRadixCons !(c (Maybe a)) !(c (InvRadixChunk c a)) !(c (InvRadixTree c a))
  | InvRadixNil
type InvRadixChunk c a = Reducible (InvRadixChunk' c a)
data InvRadixChunk' c a
  = ITop
  | IBin !Bool !Chunk !(c (InvRadixChunk c a)) !(c (RadixChunk c a)) -- Bool stands or if the taken path is right

data RadixZipper c a = RadixZipper { radixPathToChunk :: ![Chunk], radixSuper :: !(c (InvRadixTree c a)), radixSub :: !(c (RadixTree c a)) }

-- -- TODO: Don't know how effective is this
reduceChunk :: (Container c, Has (Writer Any) sig m) => RadixChunk' c a -> m (RadixChunk' c a)
reduceChunk = \case
  Tip _ (RadixTree (tryExtract -> Just Nothing) (tryExtract -> Just (readReducible -> Nil))) -> tell (Any True) $> Nil
  Bin _ (tryExtract -> Just (readReducible -> left)) (tryExtract -> Just (readReducible -> right))
    | Nil <- left -> tell (Any True) $> right -- hopefully no need to reduceChunk left/right
    | Nil <- right -> tell (Any True) $> left
  nonReducible -> pure nonReducible

reduceInvChunk :: (Container c, Has (Writer Any) sig m) => InvRadixChunk' c a -> m (InvRadixChunk' c a)
reduceInvChunk = \case
  IBin _ _ (tryExtract -> Just (readReducible -> supertree)) (tryExtract -> Just (readReducible -> Nil)) -> tell (Any True) $> supertree
  nonReducible -> pure nonReducible

-- -- Let's make accessRadix and accessRadix1?
accessRadix1 :: forall c a tree chunk. forall sig m. (Container c, Has (Writer Any) sig m)
  => (forall sig1 m1. Has (Writer Any) sig1 m1 => c (Maybe a) -> chunk -> m1 tree) -- ^ on sub, tree
  -> (forall sig1 m1. Has (Writer Any) sig1 m1 => RadixTree c a -> m1 tree) -- ^ on found, tree
  -> (forall sig1 m1. Has (Writer Any) sig1 m1 => Chunk -> [Chunk] -> m1 chunk) -- ^ on missing, chunk
  -> (forall sig1 m1. Has (Writer Any) sig1 m1 => Chunk -> tree -> m1 chunk) -- ^ on Tip, chunk
  -> (forall sig1 m1. Has (Writer Any) sig1 m1 => Bool -> Chunk -> c (RadixChunk c a) -> chunk -> m1 chunk) -- ^ on branch, chunk
  -> Chunk
  -> [Chunk]
  -> c (RadixChunk c a)
  -> m chunk
accessRadix1 onSubT onFoundT onMissingC onTipC onBranchC =
  let
    goChunk :: forall. forall sig m. Has (Writer Any) sig m => Chunk -> [Chunk] -> c (RadixChunk c a) -> m chunk
    goChunk key keys chunkM =
      let
        newBranch :: forall sig m. Has (Writer Any) sig m => Chunk -> m chunk
        newBranch exKey =
          let (mask, placeRight) = makeMask exKey key
          in onBranchC placeRight mask chunkM =<< onMissingC key keys
      in extract chunkM >>= \chunk -> reducible reduceChunk chunk \case
        Nil -> onMissingC key keys
        (Tip key2 subtree)
          | key == key2 -> onTipC key =<< goTree keys subtree
          | otherwise -> newBranch key2
        (Bin mask l r)
          | Just pickRight <- tryMask mask key
            -> onBranchC pickRight mask (if pickRight then l else r) =<< goChunk key keys (if pickRight then r else l)
          | otherwise -> newBranch mask
    goTree :: forall. forall sig m. Has (Writer Any) sig m => [Chunk] -> RadixTree c a -> m tree
    goTree [] = onFoundT
    goTree (key:keys) = \(RadixTree val chunk) -> onSubT val =<< goChunk key keys chunk
  in goChunk
{-# INLINE accessRadix1 #-}

-- TODO: use same m everywhere
-- Constructs both accessRadix1 and accessRadix versions
accessRadix :: forall c a tree chunk sig m. (Container c, Has (Writer Any) sig m)
  => (forall sig1 m1. Has (Writer Any) sig1 m1 => c (Maybe a) -> chunk -> m1 tree) -- ^ on sub, tree
  -> (forall sig1 m1. Has (Writer Any) sig1 m1 => RadixTree c a -> m1 tree) -- ^ on found, tree
  -> (forall sig1 m1. Has (Writer Any) sig1 m1 => Chunk -> [Chunk] -> m1 chunk) -- ^ on missing, chunk
  -> (forall sig1 m1. Has (Writer Any) sig1 m1 => Chunk -> tree -> m1 chunk) -- ^ on Tip, chunk
  -> (forall sig1 m1. Has (Writer Any) sig1 m1 => Bool -> Chunk -> c (RadixChunk c a) -> chunk -> m1 chunk) -- ^ on branch, chunk
  -> (Chunk -> [Chunk] -> c (RadixChunk c a) -> m chunk, [Chunk] -> RadixTree c a -> m tree)
accessRadix onSubT onFoundT onMissingC onTipC onBranchC =
  let
    var1 :: Chunk -> [Chunk] -> c (RadixChunk c a) -> m chunk
    var1 = accessRadix1 onSubT onFoundT onMissingC onTipC onBranchC
  in (var1, \case
    [] -> onFoundT
    (key:keys) -> \(RadixTree val chunk) -> onSubT val =<< var1 key keys chunk
  )
  -- \case
  -- [] -> onFoundT
  -- (key:keys) -> \(RadixTree val chunk) -> onSubT val =<< accessRadix1 onSubT onFoundT onMissingC onTipC onBranchC key keys chunk
{-# INLINE accessRadix #-}

accessInvRadix :: forall c a invtree sig m. (Container c, Has (Writer Any) sig m)
  => m invtree -- ^ impossible, on missing super invtree
  -> (Chunk -> c (Maybe a) -> c (InvRadixChunk c a) -> invtree -> m invtree) -- ^ on skip invchunk
  -> (c (Maybe a) -> c (InvRadixChunk c a) -> c (InvRadixTree c a) -> m invtree) -- ^ on invchunk
  -> [Chunk] -- current full path
  -> Int
  -> InvRadixTree c a
  -> m invtree
accessInvRadix onMissingInvTree onSkip onInvchunk =
  let
    goTree :: [Chunk] -> Int -> InvRadixTree c a -> m invtree
    goTree _  _ InvRadixNil = onMissingInvTree
    goTree [] _ _           = onMissingInvTree
    goTree _ 0 (InvRadixCons el invchunk superInvchunks) = onInvchunk el invchunk superInvchunks
    goTree (x:xs) n (InvRadixCons el invchunk superInvchunks) = onSkip x el invchunk =<< goTree xs (n-1) =<< extract superInvchunks
  in goTree . reverse
{-# INLINE accessInvRadix #-}

accessInvChunk :: forall c invchunk a sig m. (Container c, Has (Writer Any) sig m)
  => (Bool -> Chunk -> c (RadixChunk c a)    -> invchunk -> m invchunk) -- ^ on super
  -> (Bool -> Chunk -> c (InvRadixChunk c a) -> c (RadixChunk c a) -> m invchunk) -- ^ on sub
  -> Chunk -- key
  -> Chunk -- ex key
  -> c (InvRadixChunk c a)
  -> m invchunk
accessInvChunk onSuper onSub key =
  let
    goChunk :: Has (Writer Any) sig m => Chunk -> c (InvRadixChunk c a) -> m invchunk
    goChunk exKey chunkM =
      let
        newBranch :: Has (Writer Any) sig m => m invchunk
        newBranch =
          let (mask, placeRight) = makeMask exKey key
          in onSub (not placeRight) mask chunkM (construct $ mkReducible Nil)
      in extract chunkM >>= \chunk -> reducible reduceInvChunk chunk \case
        ITop -> newBranch
        IBin pickRight mask super sub
          | Just wasRight <- tryMask mask key ->
            if wasRight == pickRight -- we're guided the same way we came
              then newBranch
              else onSub pickRight mask super sub
          | otherwise -> onSuper pickRight mask sub =<< goChunk mask super
  in goChunk
{-# INLINE accessInvChunk #-}

accessRadixZipper :: forall c a chunk invchunk invtree tree zipper. forall sig m. (Container c, Has (Writer Any) sig m)
  => ([Chunk] -> c (InvRadixTree c a) -> tree -> m zipper) -- ^ on sub, zipper
  -> (Chunk -> [Chunk] -> c (RadixChunk c a) -> m chunk)
  -> ([Chunk] -> RadixTree c a -> m tree)
  -> ([Chunk] -> c (RadixTree c a) -> invtree -> m zipper) -- ^ on super, zipper
  -> (Chunk -> c (Maybe a) -> c (InvRadixChunk c a) -> invtree -> m invtree) -- ^ on super skip, invtree
  -> (Chunk -> c (Maybe a) -> c (InvRadixChunk c a) -> c (InvRadixTree c a) -> m invtree) -- ^ on found value, invtree
  -> (Chunk -> c (Maybe a) -> c (InvRadixTree c a) -> invchunk -> m invtree) -- ^ on found invchunk, invtree
  -> (Bool -> Chunk -> c (RadixChunk c a)    -> invchunk -> m invchunk) -- ^ on super, invchunk
  -> (Bool -> Chunk -> c (InvRadixChunk c a) -> chunk    -> m invchunk) -- ^ on sub, invchunk
  --
  -> [Chunk]
  -> RadixZipper c a
  -> m zipper
accessRadixZipper onSub onChunk onTree onSuper onSkip onFoundValue onFoundInvchunk onSuperInvchunk onSubInvchunk absPath zipper =
  let
    diffFor (x:xs) (y:ys)
      | x == y = diffFor xs ys
    diffFor p1 p2 = (p1, p2)
    (backSteps, relPath) = diffFor zipper.radixPathToChunk absPath
  in case backSteps of
    [] -> onSub zipper.radixPathToChunk zipper.radixSuper =<< onTree relPath =<< extract zipper.radixSub
    (exKey:_) -> onSuper zipper.radixPathToChunk zipper.radixSub =<< accessInvRadix
      (error "imposible")
      onSkip
      (case relPath of
        [] -> onFoundValue exKey
        (key:keys) -> \val chunk super -> onFoundInvchunk exKey val super =<< accessInvChunk
          onSuperInvchunk
          (\a b c d -> onSubInvchunk a b c =<< onChunk key keys d)
          key exKey chunk)
      zipper.radixPathToChunk
      (length backSteps - 1)
      (nonRe (extract zipper.radixSuper))
{-# INLINE accessRadixZipper #-}

lookupRadix' :: Container c => ([Chunk] -> RadixTree c a -> Maybe a,  [Chunk] -> RadixZipper c a -> Maybe a)
lookupRadix' = (\k rt -> nonRe (lookupRadix'' k rt), lookupRadixZipper'') where
  (lookupRadix1'', lookupRadix'') = accessRadix
    (\_ -> pure)
    (\(RadixTree a _) -> extract a)
    (\_ _ -> pure Nothing)
    (\_ -> pure)
    (\_ _ _ -> pure)
  lookupRadixZipper'' path zipper = nonRe $ accessRadixZipper
    (\_ _ -> pure)
    lookupRadix1''
    lookupRadix''
    (\_ _ -> pure)
    (\_ _ _ -> pure)
    (\_ val _ _ -> extract val)
    (\_ _ _ -> pure)
    (\_ _ _ -> pure)
    (\_ _ _ -> pure)
    path zipper
{-# INLINE lookupRadix' #-}

lookupRadix :: Container c => [Chunk] -> RadixTree c a -> Maybe a
lookupRadix = fst lookupRadix'
{-# INLINE lookupRadix #-}

lookupRadixZipper :: Container c => [Chunk] -> RadixZipper c a -> Maybe a
lookupRadixZipper = snd lookupRadix'
{-# INLINE lookupRadixZipper #-}

mkBinNonRe :: Container c => Bool -> Chunk -> c (RadixChunk c a) -> c (RadixChunk c a) -> RadixChunk' c a
mkBinNonRe right mask a b = Bin mask (if right then a else b) (if right then b else a)
{-# INLINE mkBinNonRe #-}

mkBin :: (Container c, Has (Writer Any) sig m) => Bool -> Chunk -> c (RadixChunk c a) -> c (RadixChunk c a) -> m (RadixChunk' c a)
mkBin a b c d = reduceChunk $ mkBinNonRe a b c d
{-# INLINE mkBin #-}

mkIBinNonRe :: Bool -> Chunk -> c (InvRadixChunk c a) -> c (RadixChunk c a) -> InvRadixChunk' c a
mkIBinNonRe = IBin
{-# INLINE mkIBinNonRe #-}

mkIBin :: (Container c, Has (Writer Any) sig m) => Bool -> Chunk -> c (InvRadixChunk c a) -> c (RadixChunk c a) -> m (InvRadixChunk' c a)
mkIBin a b c d = reduceInvChunk $ mkIBinNonRe a b c d

insertRadix' :: Container c => a -> ([Chunk] -> RadixTree c a -> RadixTree c a, [Chunk] -> RadixZipper c a -> RadixZipper c a)
insertRadix' val = (\k rt -> nonRe (insertRadix'' k rt), insertRadixZipper'') where
  (insertRadix1'', insertRadix'') = accessRadix
    (\a b -> pure $ RadixTree a b)
    (\(RadixTree _oldVal b) -> pure $ RadixTree (construct $ Just val) b)
    (\key1 keys2 -> pure $ snd $ foldr
      (\key sub -> (construct Nothing, construct $ mkReducible $ Tip key $ uncurry RadixTree sub))
      (construct (Just val), construct (mkReducible Nil))
      (key1:keys2))
    (\k v -> pure $ construct $ mkReducible $ Tip k v)
    (\k r a b -> pure $ construct $ mkReducible $ mkBinNonRe k r a b)
  insertRadixZipper'' path zipper = nonRe $ accessRadixZipper
      (\a b c -> pure $ RadixZipper a b (construct c))
      insertRadix1''
      insertRadix''
      (\a b c -> pure $ RadixZipper a (construct c) b)
      (\_tipOfSkipped a b c -> pure $ InvRadixCons a b $ construct c)
      (\_tipOfSkipped _ b c -> pure $ InvRadixCons (construct $ Just val) b c)
      (\_ a b c -> pure $ InvRadixCons a c b)
      (\a b c d -> pure $ construct $ mkReducible $ mkIBinNonRe a b d c)
      (\a b c d -> pure $ construct $ mkReducible $ mkIBinNonRe a b c d) -- (not a)?
      path zipper
{-# INLINE insertRadix' #-}

insertRadix :: Container c => [Chunk] -> p -> RadixTree c p -> RadixTree c p
insertRadix k v = fst (insertRadix' v) k

insertRadixZipper :: Container c => [Chunk] -> p -> RadixZipper c p -> RadixZipper c p
insertRadixZipper k v = snd (insertRadix' v) k

deleteRadix' :: Container c => ([Chunk] -> RadixTree c a -> RadixTree c a, [Chunk] -> RadixZipper c a -> RadixZipper c a)
deleteRadix' = (\k rt -> nonRe (deleteRadix'' k rt), deleteRadixZipper'') where
  (deleteRadix1'', deleteRadix'') = accessRadix
    (\a b -> pure $ RadixTree a b) -- on sub, tree
    (\(RadixTree _deleted sub) -> pure $ RadixTree (construct Nothing) sub) -- on found, tree
    (\_key1 _keys2 -> pure $ construct $ mkReducible Nil) -- on missing, chunk
    (\key tree -> pure $ construct $ mkReducible $ Tip key tree) -- on Tip, chunk
    (\k r a b -> pure $ construct $ mkReducible $ nonRe $ mkBin k r a b) -- on branch, chunk
  deleteRadixZipper'' path zipper = nonRe $ accessRadixZipper
    (\a b c -> pure $ RadixZipper a b (construct c))
    deleteRadix1''
    deleteRadix''
    (\a b c -> pure $ RadixZipper a (construct c) b)
    (\_tipOfSkipped a b c -> pure $ InvRadixCons a b $ construct c) -- on super skip, invtree
    (\_tipOfSkipped _deleted b c -> pure $ InvRadixCons (construct Nothing) b c) -- on found invchunk, invtree
    (\_ a b c -> pure $ InvRadixCons a c b)
    (\a b c d -> pure $ construct $ mkReducible $ nonRe $ mkIBin a b d c)
    (\a b c d -> pure $ construct $ mkReducible $ nonRe $ mkIBin a b c d)
    path
    zipper

deleteRadix :: Container c => [Chunk] -> RadixTree c p -> RadixTree c p
deleteRadix k = fst deleteRadix' k

deleteRadixZipper :: Container c => [Chunk] -> RadixZipper c p -> RadixZipper c p
deleteRadixZipper k = snd deleteRadix' k

-- 
focusRadixZipper :: forall c a. Container c => [Chunk] -> RadixZipper c a -> RadixZipper c a
focusRadixZipper targetPath =
  let
    applyN 0 _ x = x
    applyN n f x = applyN (n-1) f (f x)

    -- focusRadix1 :: forall sig1 m1. Has (Writer Any) sig1 m1 => Chunk -> [Chunk] -> c (RadixChunk c a) -> m1 (c (Maybe a) -> c (InvRadixChunk c a) -> c (InvRadixTree c a) -> RadixZipper c a)
    focusRadix =
      let onTipInv topval invchunk invtree = construct $ InvRadixCons topval invchunk invtree in
      accessRadix
        (\val chunk -> pure $ chunk val $ construct $ mkReducible ITop) -- on sub, tree
        (\rt -> pure \b -> RadixZipper targetPath b $ construct rt) -- on found, tree
        (\_key1 (length -> leftToPass) -> pure \topval invchunk invtree -> RadixZipper -- on missing
            targetPath
            (applyN leftToPass
              (construct . InvRadixCons (construct Nothing) (construct $ mkReducible ITop)) -- add empty trees 'length keys2' times
              (onTipInv topval invchunk invtree)) -- finish this chunk
            (construct $ RadixTree (construct Nothing) (construct $ mkReducible Nil)))
        (\_key tree -> pure \topval invchunk invtree -> tree (onTipInv topval invchunk invtree)) -- on Tip
        (\pickRight mask other picked -> pure \topval invchunk -> picked topval (construct $ mkReducible $ IBin pickRight mask invchunk other))

    revInvChunk :: Chunk -> RadixTree c a -> c (Maybe a) -> c (InvRadixChunk c a) -> RadixTree c a
    revInvChunk chunkName oldTree topval oldInvchunk =
      let
        revInvChunk' :: c (RadixChunk c a) -> c (InvRadixChunk c a) -> RadixTree c a
        revInvChunk' chunk = (readReducible . nonRe . extract) >>> \case
          ITop -> RadixTree topval chunk
          IBin pickRight mask super other -> revInvChunk' (construct $ mkReducible $ nonRe $ mkBin pickRight mask other chunk) super
      in revInvChunk' (construct $ mkReducible $ Tip chunkName oldTree) oldInvchunk
  in
    nonRe . accessRadixZipper
      (\_ initialInvT tree -> pure $ tree initialInvT) -- on sub, zipper
      (fst focusRadix)
      (snd focusRadix)
      (\_ initialT invtree -> pure $ invtree (nonRe $ extract initialT)) -- on super, zipper
      -- when we go up, we save the initial tree in a Tip. So eventually it needs to be extracted, unfortunately
      -- alternatively, we could save pointer on Tip, but the problem doesn't sound to worth it
      (\key topval invchunk invtree -> pure \tree -> invtree $ revInvChunk key tree topval invchunk) -- on skip
      (\key topval invchunk invtreeM -> pure \oldTree -> -- on found value, invtree
        RadixZipper targetPath invtreeM (construct $ revInvChunk key oldTree topval invchunk))
      (\key topval invtree invchunk -> pure $ invchunk topval invtree . construct . mkReducible . Tip key) -- on found invchunk, invtree
      (\pickRight mask other super -> pure \topval invtree chunk -> super topval invtree (construct $ mkReducible $ nonRe $ mkBin pickRight mask other chunk)) -- on super, invchunk
      (\pickRight mask super other -> pure \topval invtree chunk -> other topval (construct $ mkReducible $ nonRe $ mkIBin (not pickRight) mask super chunk) invtree) -- on sub, invchunk
      targetPath

-- TODO: monadical extract, separate RadixTree and RadixZipper into different modules, `merge`, `adjust`

emptyRadix :: Container c => RadixTree c a
emptyRadix = RadixTree (construct Nothing) (construct $ mkReducible Nil)

emptyRadixZipper :: Container c => RadixZipper c a
emptyRadixZipper = RadixZipper [] (construct InvRadixNil) (construct emptyRadix)

-- debug

-- Lazy String-based show for debug
tryExtractShow :: (Container c, Show a) => c a -> String
tryExtractShow = maybe "<>" show . tryExtract
instance (Container c, Show a) => Show (RadixTree c a) where
  show (RadixTree val chunk) = "(RadixTree (" <> tryExtractShow val <> ") " <> tryExtractShow chunk <> ")"
instance (Container c, Show a) => Show (RadixChunk' c a) where
  show = \case
    Nil -> "Nil"
    Tip key val -> "(Tip " <> show key <> " " <> show val <> ")"
    Bin mask l r -> "(Bin " <> show mask <> " " <> tryExtractShow l <> " " <> tryExtractShow r <> ")"
instance (Container c, Show a) => Show (InvRadixTree c a) where
  show = \case
    InvRadixNil -> "InvRadixNil"
    InvRadixCons topval super other -> "(InvRadixCons (" <> tryExtractShow topval <> ") " <> tryExtractShow super <> " " <> tryExtractShow other <> ")"
instance (Container c, Show a) => Show (InvRadixChunk' c a) where
  show = \case
    ITop -> "ITop"
    IBin pickRight mask super other -> "(IBin " <> show pickRight <> " " <> show mask <> " " <> tryExtractShow super <> " " <> tryExtractShow other <> ")"
instance (Container c, Show a) => Show (RadixZipper c a) where
  show (RadixZipper a b c) = "RADIX ZIPPER:\n" <> show a <> "\n" <> tryExtractShow b <> "\n" <> tryExtractShow c

showRadixZipperLookup :: (Container c, Show a) => [Chunk] -> RadixZipper c a -> String
showRadixZipperLookup = showRadixZipperLookup' where
  showRadixLookup = accessRadix
    (\val chunk -> pure $ "(onSubT " <> tryExtractShow val <> " " <> chunk <> ")")
    (\rt -> pure $ "(onFoundT " <> show rt <> ")")
    (\key keys -> pure $ "(onMissingC " <> show key <> " " <> show keys <>")")
    (\key tree -> pure $ "(onTipC " <> show key <> " " <> tree <> ")")
    (\pickRight mask other curr -> pure $ "(onBranchC " <> show pickRight <> " " <> show mask <> "" <> tryExtractShow other <> " " <> curr <> ")")
  showRadixZipperLookup' path zipper = nonRe $ accessRadixZipper
    (\k v t -> pure $ "(onSubZ " <> show k <> " " <> tryExtractShow v <> " " <> t <> ")")
    (fst showRadixLookup)
    (snd showRadixLookup)
    (\k v t -> pure $ "(onSuperZ" <> " " <> show k <> " " <> tryExtractShow v <> " " <> t <> ")")
    (\k v ic it -> pure $ "(onSkipIT " <> show k <> " " <> tryExtractShow v <> " " <> tryExtractShow ic <> " " <> it <> ")")
    (\k v ic it -> pure $ "(onFoundIT " <> show k <> " " <> tryExtractShow v <> " " <> tryExtractShow ic <> " " <> tryExtractShow it <> ")")
    (\k v it ic -> pure $ "(onFoundInvchunkIT " <> show k <> " " <> tryExtractShow v <> " " <> tryExtractShow it <> " " <> ic <> ")")
    (\pickRight mask other super -> pure $ "(onSuperIC " <> show pickRight <> " " <> show mask <> " " <> tryExtractShow other <> " " <> super <> ")")
    (\pickRight mask super other -> pure $ "(onSubIC " <> show pickRight <> " " <> show mask <> " " <> tryExtractShow super <> " " <> other <> ")")
    path
    zipper
 
 
