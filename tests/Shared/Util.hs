module Shared.Util where

import RIO hiding (runReader, ask)
import Dentrado.POC.Memory (AppIOC (..), EnvLoad (..), EnvStore (..), Env (..), sendAI, ValT (..), Val (..), AppIO)
import Dentrado.POC.Types (EventId(..), Event, Any1 (..), LocalEventId (..), Timestamp (..))
import System.IO.Unsafe (unsafePerformIO)
import qualified Dentrado.POC.Data.RadixTree as RT
import Control.Carrier.Reader (runReader, ask)
import GHC.Exts (IsList(..))
import RIO.Time (diffUTCTime, getCurrentTime)
import System.IO (putStrLn)
import Control.Algebra

measure :: Has AppIO sig m => String -> m a -> m a
measure name act = do
  start <- sendAI getCurrentTime
  res <- act
  stop <- sendAI getCurrentTime
  sendAI $ AppIOC $ lift $ putStrLn $ name <> ": " <> show @Double (1000 * realToFrac (diffUTCTime stop start)) <> "ms"
  pure res

unsafeRunAppIO :: AppIOC a -> a
unsafeRunAppIO = unsafePerformIO . runAppIO

runAppIO ∷ AppIOC a → IO a
runAppIO act = do
  env ←
    Env
      <$> newIORef 0
      <*> pure mempty
      <*> newMVar mempty
      <*> pure (EnvLoad \_ → fail "not available")
      <*> pure (EnvStore \_ → fail "not available")
      <*> newMVar RT.empty
      <*> newMVar mempty
      <*> newMVar ([], 0)
  runReader env $ unAppIOC act

putEventList ∷ [(EventId, Event)] → AppIOC ()
putEventList evs = do
  evsM ← envEvents <$> ask
  sendAI $ void $ swapMVar evsM (fmap (Any1 . Val ValTEvent) <$> fromList evs, length evs)

e ∷ Word32 → EventId
e = EventId (Timestamp 0) . LocalEventId

