import Shared.Util
import Shared.Model
import Test.QuickCheck
import RIO
import Language.Haskell.TH (newDeclarationGroup)
import Dentrado.POC.Types (SiteAccessLevel(..), Event (..))
import Dentrado.POC.Gear (runGear, confNewGear)
import qualified Dentrado.POC.StateGraph as SG
import qualified Dentrado.POC.Data.RadixTree as RT
import Dentrado.POC.Memory (AppIOC(..))
import System.IO (print)
import Dentrado.POC.Types (StateGraphEntry(..))
import qualified Control.Effect.Empty as E
import Control.Carrier.State.Strict (runState)
import Control.Effect.State (modify)

$(newDeclarationGroup)
main ∷ IO ()
main = do
  evs <- generate do
    let users = 50
    let chooseUser = e . fromIntegral <$> chooseInt (0, users-1)
    let genEntry = AdminSetAccessLevel <$> (frequency [(9, Just <$> chooseUser), (1, pure Nothing)]) <*> chooseUser <*> elements [SalUser, SalAdmin]
    changes <- vectorOf 10000 genEntry
    pure $ zipWith (\i v -> (e i, v)) [0..] (replicate users CreateUser ++ changes)

  runAppIO do
    status' ← confNewGear status ()
    putEventList evs

    SG.StateGraph sg <- measure "Process 10000" $ runGear status'

    final <- measure "Result collection" do
      perKeys <- RT.toListM sg

      runState (0 :: Int) do
        for perKeys \(k, (_, vals)) -> (k,) . join <$> RT.runNonDetMax (RT.lookup RT.selNonDet vals)
    AppIOC $ lift $ print final
