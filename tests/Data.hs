import Dentrado.POC.Data
import Test.QuickCheck

import RIO
import qualified RIO.Set as Set
import qualified RIO.Map as Map
import Control.Monad.State (StateT, get, put, execStateT)


-- Script (list of commands) to be executed on a map-like data structure to test whether it behaves correctly.
-- data MapLikeScript k v = MapLikeScript !(Set k) ![(k, MapLikeCommand v)]
-- data MapLikeCommand v = Insert !v | Delete | Lookup | Focus

-- instance Arbitrary v => Arbitrary (MapLikeCommand v) where
--   arbitrary = oneof [ Insert <$> arbitrary, pure Delete, pure Lookup, pure Focus ]
--   shrink _ = []

-- instance (Ord k, Arbitrary k, Arbitrary v) => Arbitrary (MapLikeScript k v) where
--   arbitrary = do
--     keys <- Set.fromList <$> arbitrary
--     size <- getSize
--     commands <- vectorOf (size * 5) _
--       elements (Set.toList keys)

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
  (k, Insert v) -> insertRadixZipper k v
  (k, Delete) -> deleteRadixZipper k
  (k, Focus) -> focusRadixZipper k

processScriptRadixZipper :: MapLikeScript a -> (([Maybe a], [Maybe a]), RadixZipper Identity a)
processScriptRadixZipper = processScript processCommandRadixZipper lookupRadixZipper emptyRadixZipper

processScript :: (([Chunk], MapLikeCommand v) -> t -> t) -> ([Chunk] -> t -> c) -> t -> MapLikeScript v -> (([c], [c]), t)
processScript processCommand processLookup initMap (MapLikeScript keys cmds) =
  let (finResp, finMap) = foldl'
        (\(accResps, accMap) (k, v) -> (processLookup k accMap:accResps, processCommand (k, v) accMap))
        ([], initMap)
        cmds
  in ((finResp, (`processLookup` finMap) <$> Set.toList keys), finMap)

main :: IO ()
main = do
  result <- quickCheckWithResult (stdArgs { maxSuccess = 1000 }) $
    \cmds -> fst (processScriptMap @Int cmds) == fst (processScriptRadixZipper @Int cmds)
  case result of
    Success {} -> return ()
    _ -> exitFailure
