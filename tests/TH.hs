import RIO
import Dentrado.POC.TH

$(moduleId 3)

def1 :: Word64
def1 = $sFresh

def2 :: Word64
def2 = $sFresh

def3 :: (Word64, Word64, Word64)
def3 = ($sFresh, $sFresh, $sFresh)

main :: IO ()
main = do
  let ok = def1 == 4719772409484279808 && def2 == 4719913146972635136
        && def3 == (4720053884460990464,4720194621949345792,4720335359437701120)
  unless ok exitFailure
