{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use uncurry" #-}
module Dentrado.POC.Data.RadixZipper where
import RIO hiding (mask, toList, catch)
import Control.Algebra
import Control.Effect.Writer
import Dentrado.POC.Data.Container
import Dentrado.POC.Data.RadixTree (RadixChunk, Chunk, RadixTree)
import qualified Dentrado.POC.Data.RadixTree as RT
import Control.Effect.Fresh (Fresh)
import Dentrado.POC.TH (moduleId, sRunEvalFresh)
import Control.Carrier.Writer.Church (WriterC, runWriter)
import Data.Monoid (First(..))

$(moduleId 2)

data InvRadixTree c k a
  = InvRadixCons !(c (Maybe a)) !(c (InvRadixChunk c k a)) !(c (InvRadixTree c k a))
  | InvRadixNil
type InvRadixChunk c k a = Reducible (InvRadixChunk' c k a)
data InvRadixChunk' c k a
  = ITop
  | IBin !Bool !Chunk !(c (InvRadixChunk c k a)) !(c (RadixChunk c k a)) -- Bool stands or if the taken path is right

data RadixZipper c k a = RadixZipper { radixPathToChunk :: ![Chunk], radixSuper :: !(c (InvRadixTree c k a)), radixSub :: !(c (RadixTree c k a)) }

reduceInvChunk'' :: (Container c, Has (Writer (Reduced' s)) sig m) => Proxy s -> InvRadixChunk' c k a -> m (InvRadixChunk' c k a, Maybe (c (InvRadixChunk c k a)))
reduceInvChunk'' (Proxy @s) = \case
  IBin _ _ supertree'@(tryFetchC -> Just (readReducible -> supertree)) (tryFetchC -> Just (readReducible -> RT.Nil)) -> tell (Reduced' @s True) $> (supertree, Just supertree')
  nonReducible -> pure (nonReducible, Nothing)

reduceInvChunk' :: (Container c, Has (Writer (Reduced' s)) sig m) => Proxy s -> InvRadixChunk' c k a -> m (InvRadixChunk' c k a)
reduceInvChunk' p v = fst <$> reduceInvChunk'' p v

reduceInvChunk :: (Container c, Has (Writer Reduced) sig m) => InvRadixChunk' c k a -> m (InvRadixChunk' c k a)
reduceInvChunk = reduceInvChunk' (Proxy @"")

-- Problem: copy-paste from RadixTree
allocReducedInvChunk :: (Container c1, Container c2, Has Fresh sig m) => (forall b. c2 b -> WriterC Reduced m (c1 b)) -> InvRadixChunk' c2 k a -> m (c1 (InvRadixChunk c2 k a))
allocReducedInvChunk f c = nonRe $ reduceInvChunk'' (Proxy @"") c >>= \case
  (v, Nothing) -> allocC $ mkReducible v
  (_, Just v) -> f v

accessInvRadix :: forall c k a invtree sig m. (Container c, Has (Fresh :+: Writer Reduced) sig m)
  => invtree -- ^ impossible, on missing super invtree
  -> (Chunk -> c (Maybe a) -> c (InvRadixChunk c k a) -> invtree -> invtree) -- ^ on skip invchunk
  -> (c (Maybe a) -> c (InvRadixChunk c k a) -> c (InvRadixTree c k a) -> invtree) -- ^ on invchunk
  -> [Chunk] -- current full path
  -> Int
  -> InvRadixTree c k a
  -> m invtree
accessInvRadix onMissingInvTree onSkip onInvchunk =
  let
    goTree :: [Chunk] -> Int -> InvRadixTree c k a -> m invtree
    goTree _  _ InvRadixNil = pure onMissingInvTree
    goTree [] _ _           = pure onMissingInvTree
    goTree _ 0 (InvRadixCons el invchunk superInvchunks) = pure $ onInvchunk el invchunk superInvchunks
    goTree (x:xs) n (InvRadixCons el invchunk superInvchunks) = onSkip x el invchunk <$> (goTree xs (n-1) =<< fetchC superInvchunks)
  in goTree . reverse
{-# INLINE accessInvRadix #-}

accessInvChunk :: forall c k invchunk a sig m. (Container c, Has (Fresh :+: Writer Reduced) sig m)
  => (Bool -> Chunk -> c (RadixChunk c k a)    -> invchunk -> invchunk) -- ^ on super
  -> (Bool -> Chunk -> c (InvRadixChunk c k a) -> c (RadixChunk c k a) -> invchunk) -- ^ on sub
  -> Chunk -- key
  -> Chunk -- ex key
  -> c (InvRadixChunk c k a)
  -> m invchunk
accessInvChunk onSuper onSub key =
  let
    goChunk :: Chunk -> c (InvRadixChunk c k a) -> m invchunk
    goChunk exKey chunkM =
      let
        newBranch :: invchunk
        newBranch =
          let (mask, placeRight) = RT.makeMask exKey key
          in onSub (not placeRight) mask chunkM RT.sNil
      in fetchC chunkM >>= \chunk -> reducible reduceInvChunk chunk \case
        ITop -> pure newBranch
        IBin pickRight mask super sub
          | Just wasRight <- RT.tryMask mask key ->
            if wasRight == pickRight -- we're guided the same way we came
              then pure newBranch
              else pure $ onSub pickRight mask super sub
          | otherwise -> onSuper pickRight mask sub <$> goChunk mask super
  in goChunk
{-# INLINE accessInvChunk #-}

accessRadixZipper :: forall c k a chunk invchunk invtree tree zipper sig m. (Container c, Has Fresh sig m)
  => ([Chunk] -> c (InvRadixTree c k a) -> tree -> zipper) -- ^ on sub, zipper
  -> (Chunk -> [Chunk] -> c (RadixChunk c k a) -> chunk)
  -> ([Chunk] -> RadixTree c k a -> tree)
  -> ([Chunk] -> c (RadixTree c k a) -> invtree -> zipper) -- ^ on super, zipper
  -> (Chunk -> c (Maybe a) -> c (InvRadixChunk c k a) -> invtree -> invtree) -- ^ on super skip, invtree
  -> (Chunk -> c (Maybe a) -> c (InvRadixChunk c k a) -> c (InvRadixTree c k a) -> invtree) -- ^ on found value, invtree
  -> (Chunk -> c (Maybe a) -> c (InvRadixTree c k a) -> invchunk -> invtree) -- ^ on found invchunk, invtree
  -> (Bool -> Chunk -> c (RadixChunk c k a)    -> invchunk -> invchunk) -- ^ on super, invchunk
  -> (Bool -> Chunk -> c (InvRadixChunk c k a) -> chunk    -> invchunk) -- ^ on sub, invchunk
  --
  -> [Chunk]
  -> RadixZipper c k a
  -> m zipper
accessRadixZipper onSub onChunk onTree onSuper onSkip onFoundValue onFoundInvchunk onSuperInvchunk onSubInvchunk absPath zipper = nonRe
  let
    diffFor (x:xs) (y:ys)
      | x == y = diffFor xs ys
    diffFor p1 p2 = (p1, p2)
    (backSteps, relPath) = diffFor zipper.radixPathToChunk absPath
  in case backSteps of
    [] -> onSub zipper.radixPathToChunk zipper.radixSuper . onTree relPath <$> fetchC zipper.radixSub
    (exKey:_) -> do
      radixSuper' <- fetchC zipper.radixSuper
      invRadix' <- join $ accessInvRadix
        (error "impossible")
        (\a b c d -> onSkip a b c <$> d)
        (\val chunk super -> case relPath of
          [] -> pure $ onFoundValue exKey val chunk super
          (key:keys) -> onFoundInvchunk exKey val super <$> accessInvChunk
            onSuperInvchunk
            (\a b c d -> onSubInvchunk a b c $ onChunk key keys d)
            key exKey chunk)
        zipper.radixPathToChunk
        (length backSteps - 1)
        radixSuper'
      pure $ onSuper zipper.radixPathToChunk zipper.radixSub invRadix'
{-# INLINE accessRadixZipper #-}

mkIBinNonRe :: Bool -> Chunk -> c (InvRadixChunk c k a) -> c (RadixChunk c k a) -> InvRadixChunk' c k a
mkIBinNonRe = IBin
{-# INLINE mkIBinNonRe #-}

mkIBin :: (Container c, Has (Writer Reduced) sig m) => Bool -> Chunk -> c (InvRadixChunk c k a) -> c (RadixChunk c k a) -> m (InvRadixChunk' c k a)
mkIBin a b c d = reduceInvChunk $ mkIBinNonRe a b c d

lookup :: (Container c, Has Fresh sig m) => [Chunk] -> RadixZipper c k a -> m (Maybe a)
lookup keys zipper = nonRe =<< accessRadixZipper
  (\_ _ -> id)
  (\a b c -> join $ fst RT.internalLookup a b c)
  (\a b -> join $ snd RT.internalLookup a b)
  (\_ _ -> id)
  (\_ _ _ -> id)
  (\_ val _ _ -> fetchC val)
  (\_ _ _ -> id)
  (\_ _ _ -> id)
  (\_ _ _ -> id)
  keys zipper

insert :: (Container c, Has Fresh sig m) => [Chunk] -> a -> RadixZipper c k a -> m (RadixZipper c k a)
insert path val zipper = nonRe =<< accessRadixZipper
  (\a b c -> RadixZipper a b <$> (allocC =<< c))
  (\a b c -> join $ fst (RT.internalInsert val) a b c)
  (\a b -> join $ snd (RT.internalInsert val) a b)
  (\a b c -> (\c' -> RadixZipper a c' b) <$> (allocC =<< c))
  (\_tipOfSkipped a b c -> InvRadixCons a b <$> (allocC =<< c))
  (\_tipOfSkipped _ b c -> (\val' -> InvRadixCons val' b c) <$> allocC (Just val))
  (\_ a b c -> (\c' -> InvRadixCons a c' b) <$> c)
  (\a b c d -> do
    d' <- d
    allocC $ mkReducible $ mkIBinNonRe a b d' c)
  (\a b c d -> allocC . mkReducible . mkIBinNonRe a b c =<< d)
  path zipper

update :: (Container c, Has Fresh sig m) => (c (Maybe a) -> WriterC Reduced m (c (Maybe a))) -> [Chunk] -> RadixZipper c k a -> m (RadixZipper c k a)
update f path zipper = nonRe =<< accessRadixZipper
  (\a b c -> RadixZipper a b <$> (allocC =<< c))
  (\a b c -> join $ fst (RT.internalUpdate f) a b c)
  (\a b -> join $ snd (RT.internalUpdate f) a b)
  (\a b c -> (\c' -> RadixZipper a c' b) <$> (allocC =<< c))
  (\_tipOfSkipped a b c -> InvRadixCons a b <$> (allocC =<< c))
  (\_tipOfSkipped _deleted b c -> pure $ InvRadixCons sNothing b c)
  (\_ a b c -> (\c' -> InvRadixCons a c' b) <$> c)
  (\a b c d -> do
    d' <- d
    allocC . mkReducible =<< mkIBin a b d' c)
  (\a b c d -> allocC . mkReducible =<< mkIBin a b c =<< d)
  path
  zipper

delete :: (Container c, Has Fresh sig m) => [Chunk] -> RadixZipper c k a -> m (RadixZipper c k a)
delete = update (\_ -> pure sNothing)

pop :: (Container c, Has Fresh sig m) => [Chunk] -> RadixZipper c k a -> m (Maybe a, RadixZipper c k a)
pop k rt = runWriter (\(First a) b -> pure (a, b)) $ update
  (\v -> do
    v' <- fetchC v
    tell $ First v'
    pure sNothing
  )
  k rt

sITop :: Container c => c (InvRadixChunk c k a)
sITop = $sRunEvalFresh $ allocC $ mkReducible ITop

focus :: forall c k a sig m. Has Fresh sig m => Container c => [Chunk] -> RadixZipper c k a -> m (RadixZipper c k a)
focus targetPath =
  let
    applyNM :: forall m1 a1. Monad m1 => Int -> (a1 -> m1 a1) -> a1 -> m1 a1
    applyNM 0 _ x = pure x
    applyNM n f x = applyNM (n-1) f =<< f x

    -- focusRadix :: Chunk -> [Chunk] -> c (RadixChunk c k a) -> m (c (Maybe a) -> c (InvRadixChunk c k a) -> c (InvRadixTree c k a) -> m (RadixZipper c k a))
    focusRadix = --fst $
      let onTipInv topval invchunk invtree = allocC $ InvRadixCons topval invchunk invtree
      in RT.accessRadix
        (\val chunk -> chunk val sITop)
        (\rt invtree -> RadixZipper targetPath invtree <$> allocC rt) -- on found, tree
        (\_key1 (length -> leftToPass) topval invchunk invtree -> do -- on missing
          super' <- applyNM leftToPass
            (allocC . InvRadixCons sNothing sITop) -- add empty trees 'length keys2' times
            =<< onTipInv topval invchunk invtree -- finish this chunk
          pure $ RadixZipper -- on missing
            targetPath
            super'
            RT.sEmpty)
        (\_key tree topval invchunk invtree -> tree =<< onTipInv topval invchunk invtree)
        (\pickRight mask other picked topval invchunk invtree -> (\invchunk' -> picked topval invchunk' invtree) =<< allocC . mkReducible =<< mkIBin pickRight mask invchunk other)

    revInvChunk :: Chunk -> RadixTree c k a -> c (Maybe a) -> c (InvRadixChunk c k a) -> WriterC Reduced m (RadixTree c k a)
    revInvChunk chunkName oldTree topval oldInvchunk =
      let
        revInvChunk' :: c (RadixChunk c k a) -> c (InvRadixChunk c k a) -> WriterC Reduced m (RadixTree c k a)
        revInvChunk' chunk invchunk = do
          invchunk' <- fetchC invchunk
          reducible reduceInvChunk invchunk' \case
            ITop -> pure $ RT.RadixTree topval chunk
            IBin pickRight mask super other -> (`revInvChunk'` super) =<< RT.mkBin pure pickRight mask other chunk
      in (`revInvChunk'` oldInvchunk) =<< RT.mkTip pure chunkName oldTree
  in nonRe <=< accessRadixZipper
    (\_ initialInvT tree -> tree initialInvT) -- on sub, zipper
    (\k ks chunk topval invchunk invtree ->
      fst focusRadix k ks chunk >>= \f -> f topval invchunk invtree)
    (\ks tree invtree ->
      snd focusRadix ks tree >>= \f -> f invtree)
    (\_ initialT invtree -> invtree =<< fetchC initialT) -- on super, zipper
    --   -- when we go up, we save the initial tree in a Tip. So eventually it needs to be fetchCed, unfortunately
    --   -- alternatively, we could save pointer on Tip, but the problem doesn't sound to worth it
    (\key topval invchunk invtree tree -> invtree =<< revInvChunk key tree topval invchunk) -- on skip
    (\key topval invchunk invtreeM oldTree -> -- on found value, invtree
      RadixZipper targetPath invtreeM <$> (allocC =<< revInvChunk key oldTree topval invchunk))
    (\key topval invtree invchunk rt -> invchunk topval invtree =<< RT.mkTip pure key rt)
    (\pickRight mask other super topval invtree chunk -> super topval invtree =<< RT.mkBin pure pickRight mask other chunk) -- on super, invchunk
    (\pickRight mask super other topval invtree chunk -> (\invchunk' -> other topval invchunk' invtree)  =<< allocC . mkReducible =<< mkIBin (not pickRight) mask super chunk) -- on sub, invchunk
    targetPath

empty :: Container c => RadixZipper c k a
empty = RadixZipper [] ($sRunEvalFresh $ allocC InvRadixNil) RT.sEmpty

-- debug

instance (Container c, Show a) => Show (InvRadixTree c k a) where
  show = \case
    InvRadixNil -> "InvRadixNil"
    InvRadixCons topval super other -> "(InvRadixCons (" <> RT.tryFetchShow topval <> ") " <> RT.tryFetchShow super <> " " <> RT.tryFetchShow other <> ")"
instance (Container c, Show a) => Show (InvRadixChunk' c k a) where
  show = \case
    ITop -> "ITop"
    IBin pickRight mask super other -> "(IBin " <> show pickRight <> " " <> show mask <> " " <> RT.tryFetchShow super <> " " <> RT.tryFetchShow other <> ")"
instance (Container c, Show a) => Show (RadixZipper c k a) where
  show (RadixZipper a b c) = "RADIX ZIPPER:\n" <> show a <> "\n" <> RT.tryFetchShow b <> "\n" <> RT.tryFetchShow c

showRadixZipperLookup :: forall c k a sig m. (Container c, Show a, Has Fresh sig m) => [Chunk] -> RadixZipper c k a -> m String
showRadixZipperLookup = showRadixZipperLookup' where
  showRadixLookup :: (Chunk -> [Chunk] -> c (RadixChunk c k a) -> WriterC Reduced m String, [Chunk] -> RadixTree c k a -> WriterC Reduced m String)
  showRadixLookup = RT.accessRadix
    (\val chunk -> "(onSubT " <> RT.tryFetchShow val <> " " <> chunk <> ")")
    (\rt -> "(onFoundT " <> show rt <> ")")
    (\key keys -> "(onMissingC " <> show key <> " " <> show keys <>")")
    (\key tree -> "(onTipC " <> show key <> " " <> tree <> ")")
    (\pickRight mask other curr -> "(onBranchC " <> show pickRight <> " " <> show mask <> "" <> RT.tryFetchShow other <> " " <> curr <> ")")

  showRadixZipperLookup' path zipper = nonRe =<< accessRadixZipper
    (\k v t -> t <&> \t' -> "(onSubZ " <> show k <> " " <> RT.tryFetchShow v <> " " <> t' <> ")")
    (fst showRadixLookup)
    (snd showRadixLookup)
    (\k v t -> t <&> \t' -> "(onSuperZ" <> " " <> show k <> " " <> RT.tryFetchShow v <> " " <> t' <> ")")
    (\k v ic it -> it <&> \it' -> "(onSkipIT " <> show k <> " " <> RT.tryFetchShow v <> " " <> RT.tryFetchShow ic <> " " <> it' <> ")")
    (\k v ic it -> pure $ "(onFoundIT " <> show k <> " " <> RT.tryFetchShow v <> " " <> RT.tryFetchShow ic <> " " <> RT.tryFetchShow it <> ")")
    (\k v it ic -> ic <&> \ic' -> "(onFoundInvchunkIT " <> show k <> " " <> RT.tryFetchShow v <> " " <> RT.tryFetchShow it <> " " <> ic' <> ")")
    (\pickRight mask other super -> super <&> \super' ->"(onSuperIC " <> show pickRight <> " " <> show mask <> " " <> RT.tryFetchShow other <> " " <> super' <> ")")
    (\pickRight mask super other -> other <&> \other' -> "(onSubIC " <> show pickRight <> " " <> show mask <> " " <> RT.tryFetchShow super <> " " <> other' <> ")")
    path zipper

