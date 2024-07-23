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
  let ok = def1 == 216172782113783808 && def2 == 216454257090494464
        && def3 == (216735732067205120, 217017207043915776, 217298682020626432)
  unless ok exitFailure
