import Control.Carrier.State.Strict (runState)
import qualified Dentrado.POC.Data.RadixTree as RT
import Dentrado.POC.Gear (confNewGear, runGear)
import Dentrado.POC.Memory (AppIOC (..))
import qualified Dentrado.POC.StateGraph as SG
import Dentrado.POC.Types (W (..))
import Language.Haskell.TH (newDeclarationGroup)
import RIO
import Shared.Model
import Shared.Util
import System.IO (print)
import Test.QuickCheck

$(newDeclarationGroup)
main ∷ IO ()
main = do
  evs ← generate do
    let users = 50
    let chooseUser = e . fromIntegral <$> chooseInt (0, users - 1)
    let genEntry = AdminSetAccessLevel <$> (frequency [(9, W . Just <$> chooseUser), (1, pure $ W Nothing)]) <*> chooseUser <*> elements [W SalUser, W SalAdmin]
    changes ← vectorOf 10000 genEntry
    pure $ zipWith (\i v → (e i, W v)) [0 ..] (replicate users CreateUser ++ changes)

  runAppIO do
    status' ← confNewGear status ()
    putEventList evs

    SG.StateGraph sg ← measure "Process 10000" $ runGear status'

    final ← measure "Result collection" do
      perKeys ← RT.toListM sg

      runState (0 ∷ Int) do
        for perKeys \(k, (_, vals)) → (k,) . join <$> RT.runNonDetMax (RT.lookup RT.selNonDet vals)
    AppIOC $ lift $ print final
