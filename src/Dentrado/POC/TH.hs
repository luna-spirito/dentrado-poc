module Dentrado.POC.TH where

import Control.Algebra (run)
import Control.Carrier.Fresh.Church (FreshC, evalFresh)
import Data.Bits (complement, unsafeShiftL)
import Language.Haskell.TH (Exp (..), Lit (..), Q, appE, varE)
import Language.Haskell.TH.Syntax (getQ, putQ)
import RIO

{-
This module is used to generate static identifiers for constant objects.
It is absolutely critical to only give out identifiers to constant objects.

If $sFreshI is used with a non-constant value, it will result in catastrophe
since Dentrado assumes that two objects with the same identifier are in fact equal and
interchangeable.

Identifiers for static & non-static objects are encoded in the same 64-bits, but runtime identifiers
start from 0 and go up, and static identifiers start from 2^64-1 an go down.
-}

-- Current limit: 128 modules and 256 sFresh per module
data StaticFresh = StaticFresh !Word8 !Word8

moduleId ∷ Word8 → Q [a]
moduleId x = do
  when (x >= 255) $ fail "moduleId too huge"
  getQ >>= \case
    Nothing → putQ (StaticFresh x 0) $> []
    Just (StaticFresh{}) → fail "moduleId assigned twice"

-- static fresh, should be used with care not to assign the same identifier to different values
sFresh ∷ Q Exp
sFresh =
  getQ >>= \case
    Nothing → fail "No moduleId provided"
    Just (StaticFresh modId i) → do
      let newI = i + 1
      when (newI == 0) $ fail "Out of indexes"
      putQ $ StaticFresh modId newI
      pure $ LitE $ IntegerL $ complement $ (fromIntegral modId `unsafeShiftL` 55) + (fromIntegral i `unsafeShiftL` 47)

freshI ∷ Int → FreshC Identity a → a
freshI x y = run $ evalFresh x y

-- statically evaluates `FreshC Identity x`, should be used with care
sFreshI ∷ Q Exp
sFreshI = varE 'freshI `appE` sFresh
