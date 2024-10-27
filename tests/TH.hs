import Dentrado.POC.TH
import RIO

$(moduleId 3)

def1 ∷ Word64
def1 = $sFresh

def2 ∷ Word64
def2 = $sFresh

def3 ∷ (Word64, Word64, Word64)
def3 = ($sFresh, $sFresh, $sFresh)

main ∷ IO ()
main = do
  let ok =
        def1
          == 18338657682652659712
          && def2
          == 18338516945164304384
          && def3
          == (18338376207675949056, 18338235470187593728, 18338094732699238400)
  unless ok exitFailure
