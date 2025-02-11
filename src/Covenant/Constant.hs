-- |
-- Module: Covenant.Constant
-- Copyright: (C) MLabs 2025
-- License: Apache 2.0
-- Maintainer: koz@mlabs.city, farseen@mlabs.city, sean@mlabs.city
--
-- Representation of Plutus constants in Covenant.
--
-- @since 1.0.0
module Covenant.Constant
  ( -- * Types
    AConstant (..),
    PlutusData (..),
    TyExpr (..),
  )
where

import Data.ByteString (ByteString)
import Data.Text (Text)
import Data.Vector (Vector)
import Data.Vector qualified as Vector
import Test.QuickCheck
  ( Arbitrary (arbitrary, shrink),
    Gen,
    NonNegative (NonNegative),
    chooseInt,
    getNonNegative,
    listOf,
    oneof,
    sized,
  )
import Test.QuickCheck.Instances.ByteString ()
import Test.QuickCheck.Instances.Text ()
import Test.QuickCheck.Instances.Vector ()

-- | A representation of Plutus's @Data@.
--
-- We keep this separate because it allows us not to depend on Plutus itself for
-- what amounts to a straightforward sum type.
--
-- @since 1.0.0
data PlutusData
  = PlutusConstr Integer (Vector PlutusData)
  | PlutusMap (Vector (PlutusData, PlutusData))
  | PlutusList (Vector PlutusData)
  | PlutusI Integer
  | PlutusB ByteString
  deriving stock
    ( -- | @since 1.0.0
      Eq,
      -- | @since 1.0.0
      Ord,
      -- | @since 1.0.0
      Show
    )

-- | @since 1.0.0
instance Arbitrary PlutusData where
  {-# INLINEABLE arbitrary #-}
  arbitrary = sized go
    where
      go :: Int -> Gen PlutusData
      go size
        | size <= 0 =
            oneof
              [ PlutusI <$> arbitrary,
                PlutusB <$> arbitrary
              ]
        | otherwise =
            oneof
              [ PlutusI <$> arbitrary,
                PlutusB <$> arbitrary,
                PlutusConstr . getNonNegative
                  <$> arbitrary
                  <*> (Vector.fromList <$> listOf (go $ size `quot` 2)),
                PlutusMap . Vector.fromList
                  <$> listOf ((,) <$> go (size `quot` 2) <*> go (size `quot` 2)),
                PlutusList . Vector.fromList <$> listOf (go $ size `quot` 2)
              ]
  {-# INLINEABLE shrink #-}
  shrink = \case
    PlutusConstr ix dats ->
      (PlutusConstr ix <$> shrink dats)
        <> (PlutusConstr . getNonNegative <$> shrink (NonNegative ix) <*> pure dats)
    PlutusMap kvs -> PlutusMap <$> shrink kvs
    PlutusList dats -> PlutusList <$> shrink dats
    PlutusI i -> PlutusI <$> shrink i
    PlutusB bs -> PlutusB <$> shrink bs

-- | A Plutus constant term.
--
-- @since 1.0.0
data AConstant
  = AUnit
  | ABoolean Bool
  | AnInteger Integer
  | AByteString ByteString
  | AString Text
  | APair AConstant AConstant
  | AList TyExpr (Vector AConstant)
  | AData PlutusData
  deriving stock
    ( -- | @since 1.0.0
      Eq,
      -- | @since 1.0.0
      Ord,
      -- | @since 1.0.0
      Show
    )

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
instance Arbitrary AConstant where
  {-# INLINEABLE arbitrary #-}
  arbitrary = sized go
    where
      go :: Int -> Gen AConstant
      go size
        | size <= 0 =
            oneof
              [ pure AUnit,
                ABoolean <$> arbitrary,
                AnInteger <$> arbitrary,
                AByteString <$> arbitrary,
                AString <$> arbitrary,
                AData <$> arbitrary
              ]
        | otherwise =
            oneof
              [ pure AUnit,
                ABoolean <$> arbitrary,
                AnInteger <$> arbitrary,
                AByteString <$> arbitrary,
                AString <$> arbitrary,
                APair <$> go (size `quot` 2) <*> go (size `quot` 2),
                do
                  ty <- arbitrary
                  v <- Vector.fromList <$> mkVec
                  pure $ AList ty v,
                AData <$> arbitrary
              ]
      -- Note (Koz, 23/01/2025): We need this because lists must be homogenous.
      -- For simplicity, we don't currently generate lists of pairs or lists.
      mkVec :: Gen [AConstant]
      mkVec = listOf $ do
        choice :: Int <- chooseInt (0, 5)
        case choice of
          0 -> pure AUnit
          1 -> ABoolean <$> arbitrary
          2 -> AnInteger <$> arbitrary
          3 -> AByteString <$> arbitrary
          4 -> AString <$> arbitrary
          _ -> AData <$> arbitrary
  {-# INLINEABLE shrink #-}
  shrink = \case
    AUnit -> []
    ABoolean b -> ABoolean <$> shrink b
    AnInteger i -> AnInteger <$> shrink i
    AByteString bs -> AByteString <$> shrink bs
    AString t -> AString <$> shrink t
    APair x y -> (APair x <$> shrink y) <> (APair <$> shrink x <*> pure y)
    AList ty v -> AList ty <$> shrink v
    AData dat -> AData <$> shrink dat

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
