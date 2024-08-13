{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}
import RIO
import Control.Algebra
import Test.QuickCheck
import qualified RIO.Set as Set
import qualified RIO.Map as Map
import Control.Monad.State (StateT, get, put, execStateT)
import Dentrado.POC.Data.Container ( Res, runFreshIO, FreshIOC, FreshIO, allocC, ReduceC, AppForce(..) )
import Dentrado.POC.Data.RadixZipper (RadixZipper)
import Dentrado.POC.Data.RadixTree (Chunk)
import qualified Dentrado.POC.Data.RadixZipper as RZ
import System.IO.Unsafe (unsafePerformIO)
import Language.Haskell.TH (newDeclarationGroup)
import qualified Dentrado.POC.Data.RadixTree as RT
import Dentrado.POC.TH (moduleId, sRunEvalFresh)
import qualified Data.Map.Merge.Strict as Map

$(moduleId 101)

data MapLikeCommand v = Insert !v | Delete | Focus -- todo: Pop
  deriving Show
data MapLikeSel = SelEq ![Chunk] | SelMin | SelMax
  deriving Show
data MapLikeScript v = MapLikeScript !(Set [Chunk]) ![(MapLikeSel, MapLikeCommand v)]
  deriving Show

instance Arbitrary v => Arbitrary (MapLikeCommand v) where
  arbitrary = frequency [ (2, Insert <$> arbitrary), (2, pure Delete), (1, pure Focus) ]
  shrink _ = []

chunkKeys :: Gen (Set [Chunk])
chunkKeys = do
    size <- getSize
    execStateT
      (replicateM_ ((size `div` 5) `max` 5) genNewChunkKey)
      Set.empty
  where
    genNewChunkKey :: StateT (Set [Chunk]) Gen ()
    genNewChunkKey = do
      existing <- get
      newChunk <- lift arbitrary
      newOrExtend <- lift $ elements $ Left ():if Set.null existing then [] else [Right ()]
      newKey <- case newOrExtend of
        Left () -> pure [newChunk]
        Right () -> (++ [newChunk]) <$> lift (elements $ Set.toList existing)
      put $ Set.insert newKey existing

instance (Arbitrary v) => Arbitrary (MapLikeScript v) where
  arbitrary = do
    keys <- chunkKeys
    values <- listOf $ (,) <$> sel keys <*> arbitrary
    pure $ MapLikeScript keys values
    where
      sel keys = frequency [(8, SelEq <$> elements (Set.toList keys)), (1, pure SelMin), (1, pure SelMax)]
  shrink (MapLikeScript _keys cmds) = do
    cmds' <- shrinkList (const []) cmds
    pure $ MapLikeScript (Set.fromList $ cmds' >>= \cmd -> case fst cmd of
      SelEq k -> [k]
      _nonSpecific -> []) cmds'

processScript :: Monad m => ((MapLikeSel, MapLikeCommand v) -> dt -> m dt) -> (MapLikeSel -> dt -> m out) -> dt -> MapLikeScript v -> m (([out], [out]), dt)
processScript processCommand processLookup initMap (MapLikeScript keys cmds) = do
  (finResp, finMap) <- foldM
        (\(accResps, accMap) (k, v) -> (,) <$> ((:accResps) <$> processLookup k accMap) <*> processCommand (k, v) accMap)
        ([], initMap)
        cmds
  finValues <- for (Set.toList keys) \k -> SelEq k `processLookup` finMap
  pure ((finResp, finValues), finMap)

processCommandMap :: (MapLikeSel, MapLikeCommand v) -> Map [Chunk] v -> Identity (Map [Chunk] v)
processCommandMap (k1, v1) m =
  let k2M = case k1 of
        SelEq k -> Just k
        SelMin -> fst <$> Map.lookupMin m
        SelMax -> fst <$> Map.lookupMax m
  in case k2M of
    Nothing -> pure m
    Just k2 -> case v1 of
      Insert v -> pure $ Map.insert k2 v m
      Delete -> pure $ Map.delete k2 m
      Focus -> pure m

processScriptMap :: MapLikeScript a -> Identity (([Maybe a], [Maybe a]), Map [Chunk] a)
processScriptMap = processScript processCommandMap (\case
  SelEq k -> pure . Map.lookup k
  SelMin -> pure . fmap snd . Map.lookupMin
  SelMax -> pure . fmap snd . Map.lookupMax) Map.empty

processCommandRadixZipper :: forall sig m v. Has FreshIO sig m => (MapLikeSel, MapLikeCommand v) -> RadixZipper Res [Chunk] v -> m (RadixZipper Res [Chunk] v)
processCommandRadixZipper (k, v) m =
    case k of
      SelEq k2 -> hdl $ RZ.selEq k2
      SelMin -> fmap (fromMaybe m) $ RZ.min $ hdl RZ.selChoose
      SelMax -> fmap (fromMaybe m) $ RZ.max $ hdl RZ.selChoose
  where
    hdl :: (Has FreshIO sig2 m2, RZ.SelectorZipper sel (ReduceC m2)) => sel [Chunk] RZ.SZipper -> m2 (RadixZipper Res [Chunk] v)
    hdl sel = case v of
      Insert v2 -> RZ.insert sel v2 m
      Delete -> RZ.delete sel m
      Focus -> RZ.focus sel m

unsafeRunFreshIO :: FreshIOC a -> a
unsafeRunFreshIO = unsafePerformIO . runFreshIO

processScriptRadixZipper :: Has FreshIO sig m => MapLikeScript a -> m (([Maybe a], [Maybe a]), RadixZipper Res [Chunk] a)
processScriptRadixZipper = processScript processCommandRadixZipper (\case
  SelEq k -> RZ.lookup (RZ.selEq k)
  SelMin -> fmap join . RZ.min . RZ.lookup RZ.selChoose
  SelMax -> fmap join . RZ.max . RZ.lookup RZ.selChoose) RZ.empty

prop_script_same :: MapLikeScript Int -> Bool
prop_script_same cmds = fst (runIdentity $ processScriptMap @Int cmds) == fst (unsafeRunFreshIO $ processScriptRadixZipper @_ @_ @Int cmds)

-- from/to list

prop_from_to_list_rt :: Property
prop_from_to_list_rt = withMaxSuccess 50 \(kv :: [([Chunk], Int)]) -> unsafeRunFreshIO (RT.toListM =<< RT.fromListM @Res kv) == (Map.toList $ Map.fromList kv)

data RadixZipperInp v = RadixZipperInp ![Chunk] ![([Chunk], v)]
  deriving Show

instance Arbitrary v => Arbitrary (RadixZipperInp v) where
  arbitrary = do
    ks <- Set.toList <$> chunkKeys
    kvs <- for ks \k -> (k,) <$> arbitrary
    focus <- elements ks
    pure $ RadixZipperInp focus kvs
  shrink (RadixZipperInp focus vals) = RadixZipperInp focus <$> shrinkList shrinkNothing vals

mkRadixZipper :: Has FreshIO sig m => RadixZipperInp v -> m (RadixZipper Res [Chunk] v)
mkRadixZipper (RadixZipperInp focus kvs) = RZ.focus (RZ.selEq focus) =<< RZ.fromListM kvs

prop_from_to_list_rz :: Property
prop_from_to_list_rz = withMaxSuccess 50 \inp@(RadixZipperInp @Int _ kvs) -> unsafeRunFreshIO (RZ.toAscListM =<< mkRadixZipper inp) == kvs

-- merge test
-- TODO: upgrade to RadixZipper

data MergeInput v = MergeInput ![([Chunk], v)] ![([Chunk], v)]
  deriving Show

instance Arbitrary v => Arbitrary (MergeInput v) where
  arbitrary = do
    ks <- Set.toList <$> chunkKeys
    kvs <- for ks \k ->
      (,k,)
      <$> frequency
        [ (1, pure (False, True))
        , (1, pure (True , True))
        , (2, pure (True , True))]
      <*> arbitrary
    let fil sel = kvs >>= \(part, k, v) -> guard (sel part) *> [(k, v)]
    pure $ MergeInput (fil fst) (fil snd)
  shrink (MergeInput a b) = uncurry MergeInput <$> shrink (a, b)

mergeSubRT :: RT.RadixTree Res k Int -> RT.RadixTree Res k Int -> FreshIOC (RT.RadixTree Res k Int)
mergeSubRT =
  let negateAll = $sRunEvalFresh $ fst <$> RT.wither @_ @_ @_ @Res AppForce \_ val -> allocC $ Just (-val)
  in $sRunEvalFresh $ RT.merge
    AppForce
    (RT.OnOne (\a _ -> pure a) pure)
    (RT.OnOne (\_ b -> allocC $ Just (-b)) negateAll)
    (RT.OnBoth \_ a _ b -> allocC $ Just $ a - b)

mergeSubMap :: Ord k => Map k Int -> Map k Int -> Map k Int
mergeSubMap = Map.merge (Map.mapMissing $ const id) (Map.mapMissing \_ a -> -a) (Map.zipWithMatched \_ a b -> a - b)

merge_same :: MergeInput Int -> FreshIOC (RT.RadixTree Res [Chunk] Int)
merge_same (MergeInput kvs1 kvs2) = do
  t1 <- RT.fromListM kvs1
  t2 <- RT.fromListM kvs2
  mergeSubRT t1 t2

-- prop_merge_same :: MergeInput Int -> Bool
prop_merge_same = withMaxSuccess 10000 \inp@(MergeInput kvs1 kvs2) ->
    let r2 = Map.toList $ mergeSubMap (Map.fromList kvs1) (Map.fromList kvs2)
    in unsafeRunFreshIO (RT.toListM =<< merge_same inp) == r2 -- unsafeRunFreshIO (RT.toListM =<< mergeSubRT =<< RT.fromListM kvs) == Map.toList (mergeSubMap )

-- TODO: test NonDetLRC, upgrade to radix zipper in merge test

$(newDeclarationGroup)
main :: IO ()
main = do
  ok <- $quickCheckAll
  unless ok exitFailure
