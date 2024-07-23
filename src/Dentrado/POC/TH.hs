module Dentrado.POC.TH where

import RIO
import Language.Haskell.TH
import Data.Bits
import Language.Haskell.TH.Syntax

data StaticFresh = StaticFresh !Word8 !Word8

moduleId :: Word8 -> Q [a]
moduleId x = getQ >>= \case
  Nothing -> putQ (StaticFresh x 0) $> []
  Just (StaticFresh {}) -> fail "moduleId assigned twice"

-- static fresh
sFresh :: Q Exp
sFresh = getQ >>= \case
  Nothing -> fail "No moduleId provided"
  Just (StaticFresh modId i) -> do
    let newI = i + 1
    when (newI == 0) $ fail "Out of indexes"
    putQ $ StaticFresh modId newI
    pure $ LitE $ IntegerL $ (fromIntegral modId `unsafeShiftL` 56) + (fromIntegral i `unsafeShiftL` 48)
