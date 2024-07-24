module Dentrado.POC.TH where

import RIO
import Language.Haskell.TH (Q, Exp (..), Lit (..), varE, appE)
import Language.Haskell.TH.Syntax (getQ, putQ)
import Data.Bits (unsafeShiftL)
import Control.Carrier.Fresh.Church (evalFresh, FreshC)
import Control.Algebra (run)

-- Current limit: 128 modules and 256 sFresh per module
data StaticFresh = StaticFresh !Word8 !Word8

moduleId :: Word8 -> Q [a]
moduleId x = do
  when (x >= 127) $ fail "moduleId too huge"
  getQ >>= \case
    Nothing -> putQ (StaticFresh x 0) $> []
    Just (StaticFresh {}) -> fail "moduleId assigned twice"

-- static fresh, should be used with care not to assign the same identifier to different values
sFresh :: Q Exp
sFresh = getQ >>= \case
  Nothing -> fail "No moduleId provided"
  Just (StaticFresh modId i) -> do
    let newI = i + 1
    when (newI == 0) $ fail "Out of indexes"
    putQ $ StaticFresh modId newI
    pure $ LitE $ IntegerL $ (fromIntegral modId `unsafeShiftL` 55) + (fromIntegral i `unsafeShiftL` 47) + (1 `unsafeShiftL` 62)

runEvalFresh :: Int -> FreshC Identity a -> a
runEvalFresh x y = run $ evalFresh x y

-- statically evaluates `FreshC Identity x`, should be used with care
sRunEvalFresh :: Q Exp
sRunEvalFresh = varE 'runEvalFresh `appE` sFresh
