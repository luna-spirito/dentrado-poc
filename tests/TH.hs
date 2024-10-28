import Dentrado.POC.TH
import RIO
import Control.Effect.Fresh (fresh)

$(moduleId 0)

def1 ∷ Word64
def1 = $sFresh

def2 ∷ Word64
def2 = $sFresh

def3 ∷ (Word64, Word64, Word64)
def3 = ($sFresh, $sFresh, $sFresh)

def4 :: Int
def4 = $sFreshI fresh

main ∷ IO ()
main = do
  let ok =
        def1
          == 18446744073709551615
          && def2
          == 18446603336221196287
          && def3
          == (18446462598732840959,18446321861244485631,18446181123756130303)
  unless ok exitFailure
