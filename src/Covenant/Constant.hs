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
import Test.QuickCheck (Arbitrary (arbitrary, shrink), oneof)
import Test.QuickCheck.Instances.ByteString ()

-- | A Plutus constant term.
--
-- @since 1.0.0
data AConstant
  = AUnit
  | ABoolean Bool
  | AnInteger Integer
  | AByteString ByteString
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
  arbitrary =
    oneof
      [ pure AUnit,
        ABoolean <$> arbitrary,
        AnInteger <$> arbitrary,
        AByteString <$> arbitrary
      ]
  {-# INLINEABLE shrink #-}
  shrink = \case
    AUnit -> []
    ABoolean b -> ABoolean <$> shrink b
    AnInteger i -> AnInteger <$> shrink i
    AByteString bs -> AByteString <$> shrink bs
