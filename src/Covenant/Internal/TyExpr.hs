module Covenant.Internal.TyExpr
  ( TyExpr (..),
  )
where

import Test.QuickCheck (Arbitrary (arbitrary), Gen, oneof, sized)

-- | The type of Plutus expressions.
--
-- @since 1.0.0
data TyExpr
  = TyUnit
  | TyBoolean
  | TyInteger
  | TyByteString
  | TyString
  | TyPair TyExpr TyExpr
  | TyList TyExpr
  | TyPlutusData
  | TyBLS12_381G1Element
  | TyBLS12_381G2Element
  | TyBLS12_381PairingMLResult
  deriving stock
    ( -- | @since 1.0.0
      Eq,
      -- | @since 1.0.0
      Ord,
      -- | @since 1.0.0
      Show
    )

-- | @since 1.0.0
instance Arbitrary TyExpr where
  {-# INLINEABLE arbitrary #-}
  arbitrary = sized go
    where
      go :: Int -> Gen TyExpr
      go size
        | size <= 0 =
            oneof
              [ pure TyUnit,
                pure TyBoolean,
                pure TyInteger,
                pure TyByteString,
                pure TyString,
                pure TyPlutusData
              ]
        | otherwise =
            oneof
              [ pure TyUnit,
                pure TyBoolean,
                pure TyInteger,
                pure TyByteString,
                pure TyString,
                pure TyPlutusData,
                do
                  a <- go (size `quot` 2)
                  b <- go (size `quot` 2)
                  pure $ TyPair a b,
                TyList <$> go (size - 1)
              ]
