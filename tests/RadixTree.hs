import RIO
import qualified RIO.Set as Set
import qualified RIO.Map as Map
import Control.Monad.State (StateT, get, put, execStateT)
import Dentrado.POC.Data.RadixZipper (RadixZipper)
import Dentrado.POC.Data.RadixTree (Chunk)
import qualified Dentrado.POC.Data.RadixZipper as RZ
import Test.QuickCheck

data MapLikeCommand v = Insert !v | Delete | Focus
  deriving Show
data MapLikeScript v = MapLikeScript !(Set [Chunk]) [([Chunk], MapLikeCommand v)]
  deriving Show

instance Arbitrary v => Arbitrary (MapLikeCommand v) where
  arbitrary = oneof [ Insert <$> arbitrary, pure Delete, pure Focus ]
  shrink _ = []

instance (Arbitrary v) => Arbitrary (MapLikeScript v) where
  arbitrary = do
    size <- getSize
    keys <- execStateT
      (replicateM_ ((size `div` 5) `max` 5) genNewChunkKey)
      Set.empty
    values <- vectorOf size $ (,) <$> elements (Set.toList keys) <*> arbitrary
    pure $ MapLikeScript keys values
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
  shrink (MapLikeScript _keys cmds) = do
    cmds' <- shrink cmds
    pure $ MapLikeScript (Set.fromList $ fst <$> cmds') cmds'

processCommandMap :: ([Chunk], MapLikeCommand v) -> Map [Chunk] v -> Map [Chunk] v
processCommandMap = \case
  (k, Insert v) -> Map.insert k v
  (k, Delete) -> Map.delete k
  (_, Focus) -> id

processScriptMap :: MapLikeScript a -> (([Maybe a], [Maybe a]), Map [Chunk] a)
processScriptMap = processScript processCommandMap Map.lookup Map.empty

processCommandRadixZipper :: ([Chunk], MapLikeCommand v) -> RadixZipper Identity v -> RadixZipper Identity v
processCommandRadixZipper = \case
  (k, Insert v) -> RZ.insert k v
  (k, Delete) -> RZ.delete k
  (k, Focus) -> RZ.focus k

processScriptRadixZipper :: MapLikeScript a -> (([Maybe a], [Maybe a]), RadixZipper Identity a)
processScriptRadixZipper = processScript processCommandRadixZipper RZ.lookup RZ.empty

processScript :: (([Chunk], MapLikeCommand v) -> t -> t) -> ([Chunk] -> t -> c) -> t -> MapLikeScript v -> (([c], [c]), t)
processScript processCommand processLookup initMap (MapLikeScript keys cmds) =
  let (finResp, finMap) = foldl'
        (\(accResps, accMap) (k, v) -> (processLookup k accMap:accResps, processCommand (k, v) accMap))
        ([], initMap)
        cmds
  in ((finResp, (`processLookup` finMap) <$> Set.toList keys), finMap)

prop_script_same :: MapLikeScript Int -> Bool
prop_script_same cmds = fst (processScriptMap @Int cmds) == fst (processScriptRadixZipper @Int cmds)

return []
main :: IO ()
main = do
  ok <- $quickCheckAll
  unless ok exitFailure
