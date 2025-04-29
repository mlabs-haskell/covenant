-- |
-- Module: Covenant.Test
-- Copyright: (C) MLabs 2025
-- License: Apache 2.0
-- Maintainer: koz@mlabs.city, sean@mlabs.city
--
-- Utilities designed to help test Covenant itself.
--
-- @since 1.0.0
module Covenant.Test
  ( Concrete (Concrete),
  )
where

import Control.Applicative ((<|>))
import Covenant.Index (count0)
import Covenant.Type
  ( AbstractTy,
    BuiltinFlatT
      ( BLS12_381_G1_ElementT,
        BLS12_381_G2_ElementT,
        BLS12_381_MlResultT,
        BoolT,
        ByteStringT,
        IntegerT,
        StringT,
        UnitT
      ),
    CompT (Comp0, CompN),
    CompTBody (ArgsAndResult),
    ValT (Abstraction, BuiltinFlat, ThunkT),
  )
import Data.Coerce (coerce)
import Data.Vector qualified as Vector
import Test.QuickCheck
  ( Arbitrary (arbitrary, shrink),
    Gen,
    elements,
    liftArbitrary,
    oneof,
    sized,
  )
import Test.QuickCheck.Instances.Vector ()

-- | Wrapper for 'ValT' to provide an 'Arbitrary' instance to generate only
-- value types without any type variables.
--
-- @since 1.0.0
newtype Concrete = Concrete (ValT AbstractTy)
  deriving
    ( -- | @since 1.0.0
      Eq
    )
    via (ValT AbstractTy)
  deriving stock
    ( -- | @since 1.0.0
      Show
    )

-- | @since 1.0.0
instance Arbitrary Concrete where
  {-# INLINEABLE arbitrary #-}
  arbitrary = Concrete <$> sized go
    where
      go :: Int -> Gen (ValT AbstractTy)
      go size
        | size <= 0 =
            BuiltinFlat
              <$> elements
                [ UnitT,
                  BoolT,
                  IntegerT,
                  StringT,
                  ByteStringT,
                  BLS12_381_G1_ElementT,
                  BLS12_381_G2_ElementT,
                  BLS12_381_MlResultT
                ]
        | otherwise =
            oneof
              [ pure . BuiltinFlat $ UnitT,
                pure . BuiltinFlat $ BoolT,
                pure . BuiltinFlat $ IntegerT,
                pure . BuiltinFlat $ StringT,
                pure . BuiltinFlat $ ByteStringT,
                pure . BuiltinFlat $ BLS12_381_G1_ElementT,
                pure . BuiltinFlat $ BLS12_381_G2_ElementT,
                pure . BuiltinFlat $ BLS12_381_MlResultT,
                ThunkT . Comp0 <$> (ArgsAndResult <$> liftArbitrary (go (size `quot` 4)) <*> go (size `quot` 4))
              ]
  {-# INLINEABLE shrink #-}
  shrink (Concrete v) =
    Concrete <$> case v of
      -- impossible
      Abstraction _ -> []
      ThunkT (CompN _ (ArgsAndResult args result)) ->
        ThunkT . CompN count0 <$> do
          let argsList = Vector.toList args
          argsList' <- fmap coerce . shrink . fmap Concrete $ argsList
          result' <- fmap coerce . shrink . Concrete $ result
          let args' = Vector.fromList argsList'
          pure (ArgsAndResult args' result) <|> pure (ArgsAndResult args result')
      -- Can't shrink this
      BuiltinFlat _ -> []
