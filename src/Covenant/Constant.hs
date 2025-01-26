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
  ( AConstant (..),
  )
where

import Data.ByteString (ByteString)
import Data.Text (Text)
import Data.Vector (Vector)
import Data.Vector qualified as Vector
import Test.QuickCheck
  ( Arbitrary (arbitrary, shrink),
    Gen,
    chooseInt,
    listOf,
    oneof,
    sized,
  )
import Test.QuickCheck.Instances.ByteString ()
import Test.QuickCheck.Instances.Text ()
import Test.QuickCheck.Instances.Vector ()

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
  | AList (Vector AConstant)
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
                AString <$> arbitrary
              ]
        | otherwise =
            oneof
              [ pure AUnit,
                ABoolean <$> arbitrary,
                AnInteger <$> arbitrary,
                AByteString <$> arbitrary,
                AString <$> arbitrary,
                APair <$> go (size `quot` 2) <*> go (size `quot` 2),
                AList . Vector.fromList <$> mkVec
              ]
      -- Note (Koz, 23/01/2025): We need this because lists must be homogenous.
      -- For simplicity, we don't currently generate lists of pairs or lists.
      mkVec :: Gen [AConstant]
      mkVec = listOf $ do
        choice :: Int <- chooseInt (0, 4)
        case choice of
          0 -> pure AUnit
          1 -> ABoolean <$> arbitrary
          2 -> AnInteger <$> arbitrary
          3 -> AByteString <$> arbitrary
          _ -> AString <$> arbitrary
  {-# INLINEABLE shrink #-}
  shrink = \case
    AUnit -> []
    ABoolean b -> ABoolean <$> shrink b
    AnInteger i -> AnInteger <$> shrink i
    AByteString bs -> AByteString <$> shrink bs
    AString t -> AString <$> shrink t
    APair x y -> (APair x <$> shrink y) <> (APair <$> shrink x <*> pure y)
    AList v -> AList <$> shrink v
