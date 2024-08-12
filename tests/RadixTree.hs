import RIO
import Control.Algebra
import Test.QuickCheck
import qualified RIO.Set as Set
import qualified RIO.Map as Map
import Control.Monad.State (StateT, get, put, execStateT)
import Dentrado.POC.Data.Container ( Res, runFreshIO, FreshIOC, FreshIO )
import Dentrado.POC.Data.RadixZipper (RadixZipper)
import Dentrado.POC.Data.RadixTree (Chunk)
import qualified Dentrado.POC.Data.RadixZipper as RZ
import System.IO.Unsafe (unsafePerformIO)
import Dentrado.POC.Data.Container (ReduceC)

data MapLikeCommand v = Insert !v | Delete | Focus -- todo: Pop
  deriving Show
data MapLikeSel = SelEq ![Chunk] | SelMin
  deriving Show
data MapLikeScript v = MapLikeScript !(Set [Chunk]) ![(MapLikeSel, MapLikeCommand v)]
  deriving Show

instance Arbitrary v => Arbitrary (MapLikeCommand v) where
  arbitrary = frequency [ (2, Insert <$> arbitrary), (2, pure Delete), (1, pure Focus) ]
  shrink _ = []

instance (Arbitrary v) => Arbitrary (MapLikeScript v) where
  arbitrary = do
    size <- getSize
    keys <- execStateT
      (replicateM_ ((size `div` 5) `max` 5) genNewChunkKey)
      Set.empty
    values <- vectorOf size $ (,) <$> sel keys <*> arbitrary
    pure $ MapLikeScript keys values
    where
      sel keys = frequency [(8, SelEq <$> elements (Set.toList keys)), (3, pure SelMin)]
      genNewChunkKey :: StateT (Set [Chunk]) Gen ()
      genNewChunkKey = do
        existing <- get
        newChunk <- lift arbitrary
        newOrExtend <- lift $ elements $ Left ():if Set.null existing then [] else [Right ()]
        newKey <- case newOrExtend of
          Left () -> pure [newChunk]
          Right () -> (++ [newChunk]) <$> lift (elements $ Set.toList existing)
        put $ Set.insert newKey existing
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
  in case k2M of
    Nothing -> pure m
    Just k2 -> case v1 of
      Insert v -> pure $ Map.insert k2 v m
      Delete -> pure $ Map.delete k2 m
      Focus -> pure m

processScriptMap :: MapLikeScript a -> Identity (([Maybe a], [Maybe a]), Map [Chunk] a)
processScriptMap = processScript processCommandMap (\case
  SelEq k -> pure . Map.lookup k
  SelMin -> pure . fmap snd . Map.lookupMin) Map.empty

processCommandRadixZipper :: forall sig m v. Has FreshIO sig m => (MapLikeSel, MapLikeCommand v) -> RadixZipper Res [Chunk] v -> m (RadixZipper Res [Chunk] v)
processCommandRadixZipper (k, v) m = 
    case k of
      SelEq k2 -> hdl $ RZ.selEq k2
      SelMin -> fmap (fromMaybe m) $ RZ.min $ hdl RZ.selChoose
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
  SelMin -> fmap join . RZ.min . RZ.lookup RZ.selChoose) RZ.empty

prop_script_same :: MapLikeScript Int -> Bool
prop_script_same cmds = fst (runIdentity $ processScriptMap @Int cmds) == fst (unsafeRunFreshIO $ processScriptRadixZipper @_ @_ @Int cmds)

return []
main :: IO ()
main = do
  ok <- $quickCheckAll
  unless ok exitFailure
