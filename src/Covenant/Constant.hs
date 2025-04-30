-- |
-- Module: Covenant.Constant
-- Copyright: (C) MLabs 2025
-- License: Apache 2.0
-- Maintainer: koz@mlabs.city, sean@mlabs.city
--
-- Representation of Plutus constants in Covenant.
--
-- @since 1.0.0
module Covenant.Constant
  ( -- * Types
    AConstant (..),

    -- * Functions
    typeConstant,
  )
where

import Covenant.Internal.Type
  ( BuiltinFlatT (BoolT, ByteStringT, IntegerT, StringT, UnitT),
    ValT (BuiltinFlat),
  )
import Data.ByteString (ByteString)
import Data.Kind (Type)
import Data.Text (Text)
import Test.QuickCheck
  ( Arbitrary (arbitrary, shrink),
    oneof,
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
  deriving stock
    ( -- | @since 1.0.0
      Eq,
      -- | @since 1.0.0
      Ord,
      -- | @since 1.0.0
      Show
    )

instance Arbitrary AConstant where
  {-# INLINEABLE arbitrary #-}
  arbitrary =
    oneof
      [ pure AUnit,
        ABoolean <$> arbitrary,
        AnInteger <$> arbitrary,
        AByteString <$> arbitrary,
        AString <$> arbitrary
      ]
  {-# INLINEABLE shrink #-}
  shrink = \case
    AUnit -> []
    ABoolean b -> ABoolean <$> shrink b
    AnInteger i -> AnInteger <$> shrink i
    AByteString bs -> AByteString <$> shrink bs
    AString t -> AString <$> shrink t

-- | Produce the type of a given constant.
--
-- @since 1.0.0
typeConstant ::
  forall (a :: Type).
  AConstant -> ValT a
typeConstant =
  BuiltinFlat . \case
    AUnit -> UnitT
    ABoolean _ -> BoolT
    AnInteger _ -> IntegerT
    AByteString _ -> ByteStringT
    AString _ -> StringT
