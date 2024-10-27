{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}
import RIO hiding (runReader)
import Control.Algebra
import Test.QuickCheck
import qualified RIO.Set as Set
import qualified RIO.Map as Map
import Control.Monad.State (StateT, get, put, execStateT)
import System.IO.Unsafe (unsafePerformIO)
import Language.Haskell.TH (newDeclarationGroup)
import qualified Dentrado.POC.Data.RadixTree as RT
import Dentrado.POC.TH (moduleId, sFreshI)
import qualified Data.Map.Merge.Strict as Map
import Dentrado.POC.Types (Chunk, RadixTree)
import Dentrado.POC.Memory (Res, AppIOC, AppIO, AppForce (..), allocC, ReduceC, unAppIOC, Ser, EnvStore(..), InferValT, EnvLoad(..), Env(..), sNothing, wrapB)
import qualified Dentrado.POC.Types as RT
import Control.Carrier.Reader (runReader)
import Control.Carrier.NonDet.Church (runNonDetA)

$(moduleId 101)

data MapLikeCommand v = Insert !v | Delete -- | Focus -- todo: Pop
  deriving Show
data MapLikeSel = SelEq ![Chunk] | SelMin | SelMax
  deriving Show
data MapLikeScript v = MapLikeScript !(Set [Chunk]) ![(MapLikeSel, MapLikeCommand v)]
  deriving Show

instance Arbitrary v => Arbitrary (MapLikeCommand v) where
  arbitrary = frequency [ (2, Insert <$> arbitrary), (2, pure Delete) ]
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
      -- Focus -> pure m

processScriptMap :: MapLikeScript a -> Identity (([Maybe a], [Maybe a]), Map [Chunk] a)
processScriptMap = processScript processCommandMap (\case
  SelEq k -> pure . Map.lookup k
  SelMin -> pure . fmap snd . Map.lookupMin
  SelMax -> pure . fmap snd . Map.lookupMax) Map.empty

processCommandRadixTree :: forall sig m v. (Has AppIO sig m, Ser v) => (MapLikeSel, MapLikeCommand v) -> RadixTree Res [Chunk] v -> m (RadixTree Res [Chunk] v)
processCommandRadixTree (k, v) m =
    case k of
      SelEq k2 -> hdl $ RT.selEq k2
      SelMin -> fmap (fromMaybe m) $ RT.runNonDetMin $ hdl RT.selNonDet
      SelMax -> fmap (fromMaybe m) $ RT.runNonDetMax $ hdl RT.selNonDet
  where
    hdl :: (Has AppIO sig2 m2, RT.Selector sel (ReduceC m2)) => sel [Chunk] RT.STree -> m2 (RadixTree Res [Chunk] v)
    hdl sel = case v of
      Insert v2 -> RT.insert sel v2 m
      Delete -> RT.delete sel m
      -- Focus -> RT.focus sel m

unsafeRunAppIO :: AppIOC a -> a
unsafeRunAppIO = unsafePerformIO . runReader env . unAppIOC
  where
    env = Env
      (unsafePerformIO $ newIORef 0)
      mempty
      (unsafePerformIO $ newMVar mempty)
      (EnvLoad \_ -> fail "not available")
      (EnvStore \_ -> fail "not available")
      (unsafePerformIO $ newMVar RT.empty)
      (unsafePerformIO $ newMVar mempty)
      (unsafePerformIO $ newMVar ([], 0))

processScriptRadixTree :: (Has AppIO sig m, Ser a) => MapLikeScript a -> m (([Maybe a], [Maybe a]), RadixTree Res [Chunk] a)
processScriptRadixTree = processScript processCommandRadixTree (\case
  SelEq k -> RT.lookup (RT.selEq k)
  SelMin -> fmap join . RT.runNonDetMin . RT.lookup RT.selNonDet
  SelMax -> fmap join . RT.runNonDetMax . RT.lookup RT.selNonDet) RT.empty

prop_script_same :: MapLikeScript Int -> Bool
prop_script_same cmds = fst (runIdentity $ processScriptMap @Int cmds) == fst (unsafeRunAppIO $ processScriptRadixTree @_ @_ @Int cmds)

-- PROP: from/to list
data RadixTreeInp v = RadixTreeInp ![([Chunk], v)]
  deriving Show

instance Arbitrary v => Arbitrary (RadixTreeInp v) where
  arbitrary = do
    ks <- Set.toList <$> chunkKeys
    kvs <- for ks \k -> (k,) <$> arbitrary
    pure $ RadixTreeInp kvs
  shrink (RadixTreeInp vals) = RadixTreeInp <$> shrinkList shrinkNothing vals

prop_from_to_list_rt :: Property
prop_from_to_list_rt = withMaxSuccess 50 \(RadixTreeInp @Int kvs) -> unsafeRunAppIO (RT.toListM =<< RT.fromListM @Res kvs) == (Map.toAscList $ Map.fromList kvs)

-- PROP: merge
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

mergeSubRT :: (InferValT k, Typeable k) => RT.RadixTree Res k Int -> RT.RadixTree Res k Int -> AppIOC (RT.RadixTree Res k Int)
mergeSubRT =
  $sFreshI $ RT.merge
    AppForce
    RT.onOneKeep
    ($sFreshI $ RT.onOneWitherM AppForce \_ b -> allocC $ Just (- b))
    (RT.OnBoth \_ a _ b -> allocC $ Just $ a - b)
    (Just $ RT.OnSame (\_ _ -> pure $ wrapB sNothing) (\_ _ -> pure $ wrapB sNothing) (\_ _ -> pure $ wrapB RT.sNil) (\_ _ -> pure $ wrapB RT.sNil))

mergeSubMap :: Ord k => Map k Int -> Map k Int -> Map k Int
mergeSubMap = Map.merge (Map.mapMissing $ const id) (Map.mapMissing \_ a -> -a) (Map.zipWithMatched \_ a b -> a - b)

merge_same :: MergeInput Int -> AppIOC (RT.RadixTree Res [Chunk] Int)
merge_same (MergeInput kvs1 kvs2) = do
  t1 <- RT.fromListM kvs1
  t2 <- RT.fromListM kvs2
  mergeSubRT t1 t2

prop_merge_same :: MergeInput Int -> Bool
prop_merge_same = \inp@(MergeInput kvs1 kvs2) ->
    let r2 = Map.toList $ mergeSubMap (Map.fromList kvs1) (Map.fromList kvs2)
    in unsafeRunAppIO (RT.toListM =<< merge_same inp) == r2

-- PROP: inverse ranged iteration
data RadixTreeRangeInp v = RadixTreeRangeInp !(RadixTreeInp v) !RT.RangeT
  deriving Show

instance Arbitrary v => Arbitrary (RadixTreeRangeInp v) where
  arbitrary = do
    inp@(RadixTreeInp kvs) <- arbitrary
    let mkBound = oneof [pure RT.RBUnrestricted, RT.RBRestricted <$> arbitrary <*> (fst <$> elements kvs)]
    RadixTreeRangeInp inp <$> ((,) <$> mkBound <*> mkBound)

inv_ranged_sel_rt :: Ser v => RadixTreeRangeInp v -> [([Chunk], v)]
inv_ranged_sel_rt (RadixTreeRangeInp (RadixTreeInp kvs) range) =
  unsafeRunAppIO do
    rt <- RT.fromListM @Res kvs
    fmap catMaybes $ runNonDetA @[] $ RT.reverseNonDet $ RT.lookupKV (RT.selNonDetRanged range) rt

inv_ranged_sel_stupid :: RadixTreeRangeInp a -> [([Chunk], a)]
inv_ranged_sel_stupid (RadixTreeRangeInp (RadixTreeInp kvs) (lbound, rbound)) =
  let withinLeft = \case
        RT.RBUnrestricted -> const True
        RT.RBRestricted True y -> \x -> y <= x
        RT.RBRestricted False y -> \x -> y < x
      withinRight = \case
        RT.RBUnrestricted -> const True
        RT.RBRestricted True y -> \x -> x <= y
        RT.RBRestricted False y -> \x -> x < y
  in Map.toDescList $ Map.filterWithKey (\k _ -> withinLeft lbound k && withinRight rbound k) $ Map.fromList kvs

prop_inv_ranged_sel_same :: RadixTreeRangeInp Int -> Bool
prop_inv_ranged_sel_same = \(a :: RadixTreeRangeInp Int) -> inv_ranged_sel_rt a == inv_ranged_sel_stupid a

-- TODO: test NonDetLRC, upgrade to radix zipper in merge test

$(newDeclarationGroup)
main :: IO ()
main = do
  ok <- $quickCheckAll
  unless ok exitFailure
