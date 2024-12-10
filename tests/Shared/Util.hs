module Shared.Util where

import Control.Algebra
import Control.Carrier.Reader (ask, runReader)
import qualified Dentrado.POC.Data.RadixTree as RT
import Dentrado.POC.Memory (AppIO, AppIOC (..), Env (..), EnvLoad (..), EnvStore (..), InferValT, Val (..), inferValT, sendAI)
import Dentrado.POC.Types (Any1 (..), EventId (..), LocalEventId (..), Timestamp (..))
import GHC.Exts (IsList (..))
import RIO hiding (ask, runReader)
import RIO.Time (diffUTCTime, getCurrentTime)
import System.IO (putStrLn)
import System.IO.Unsafe (unsafePerformIO)

measure ∷ (Has AppIO sig m) ⇒ String → m a → m a
measure name act = do
  start ← sendAI getCurrentTime
  res ← act
  stop ← sendAI getCurrentTime
  sendAI $ AppIOC $ lift $ putStrLn $ name <> ": " <> show @Double (1000 * realToFrac (diffUTCTime stop start)) <> "ms"
  pure res

unsafeRunAppIO ∷ AppIOC a → a
unsafeRunAppIO = unsafePerformIO . runAppIO

runAppIO ∷ AppIOC a → IO a
runAppIO act = do
  env ←
    Env
      <$> newIORef 0
      <*> pure mempty
      <*> newMVar mempty
      <*> pure (EnvLoad \_ _ → fail "not available")
      <*> pure (EnvStore \_ → fail "not available")
      <*> newMVar RT.empty
      <*> newMVar mempty
      <*> newMVar ([], 0)
  runReader env $ unAppIOC act

putEventList ∷ (InferValT True x) ⇒ [(EventId, x)] → AppIOC ()
putEventList evs = do
  evsM ← envEvents <$> ask
  sendAI $ void $ swapMVar evsM (fmap (Any1 . Val inferValT) <$> fromList evs, length evs)

e ∷ Word32 → EventId
e = EventId (Timestamp 0) . LocalEventId
