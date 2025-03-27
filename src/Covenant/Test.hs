module Covenant.Test
  ( Concrete (Concrete),
  )
where

import Covenant.Index (count0)
import Covenant.Type
  ( AbstractTy,
    BuiltinFlatT
      ( BLS12_381_G1_ElementT,
        BLS12_381_G2_ElementT,
        BLS12_381_MlResultT,
        BoolT,
        ByteStringT,
        DataT,
        IntegerT,
        StringT,
        UnitT
      ),
    BuiltinNestedT (ListT, PairT),
    CompT (CompT),
    ValT (Abstraction, BuiltinFlat, BuiltinNested, ThunkT),
  )
import Data.Coerce (coerce)
import Data.Vector qualified as Vector
import Data.Vector.NonEmpty qualified as NonEmpty
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
                  BLS12_381_MlResultT,
                  DataT
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
                pure . BuiltinFlat $ DataT,
                BuiltinNested . ListT count0 <$> go (size `quot` 4),
                BuiltinNested <$> (PairT <$> go (size `quot` 4) <*> go (size `quot` 4)),
                ThunkT . CompT count0 <$> (NonEmpty.consV <$> go (size `quot` 4) <*> liftArbitrary (go (size `quot` 4)))
              ]
  {-# INLINEABLE shrink #-}
  shrink (Concrete v) =
    Concrete <$> case v of
      -- impossible
      Abstraction _ -> []
      ThunkT (CompT _ ts) ->
        -- Note (Koz, 06/04/2025): This is needed because non-empty Vectors
        -- don't have Arbitrary instances.
        ThunkT . CompT count0 <$> do
          let asList = NonEmpty.toList ts
          shrunk <- fmap coerce . shrink . fmap Concrete $ asList
          case shrunk of
            [] -> []
            x : xs -> pure (NonEmpty.consV x . Vector.fromList $ xs)
      -- Can't shrink this
      BuiltinFlat _ -> []
      BuiltinNested t -> case t of
        ListT _ t' -> do
          Concrete shrunk <- shrink (Concrete t')
          pure . BuiltinNested . ListT count0 $ shrunk
        PairT t1 t2 -> do
          Concrete shrunkT1 <- shrink (Concrete t1)
          Concrete shrunkT2 <- shrink (Concrete t2)
          [ BuiltinNested $ PairT shrunkT1 t2,
            BuiltinNested $ PairT t1 shrunkT2,
            shrunkT1,
            shrunkT2
            ]
