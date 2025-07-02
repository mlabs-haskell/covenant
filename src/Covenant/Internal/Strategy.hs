module Covenant.Internal.Strategy
  ( DataEncoding (..),
    PlutusDataStrategy (..),
    InternalStrategy (..),
    PlutusDataConstructor (..),
  )
where

-- | @since 1.1.0
data DataEncoding
  = SOP
  | PlutusData PlutusDataStrategy
  | BuiltinStrategy InternalStrategy
  deriving stock
    ( -- | @since 1.1.0
      Show,
      -- | @since 1.1.0
      Eq,
      -- | @since 1.1.0
      Ord
    )

-- NOTE: Wrapped data-primitive (Integer + ByteString) require a special case for their encoders, which was originally
--       part of a "WrapperData" strategy here which we generalized to the NewtypeData strategy.

-- | @since 1.1.0
data PlutusDataStrategy
  = EnumData
  | ProductListData
  | ConstrData
  | NewtypeData
  deriving stock
    ( -- | @since 1.1.0
      Show,
      -- | @since 1.1.0
      Eq,
      -- | @since 1.1.0
      Ord
    )

-- | @since 1.1.0
data PlutusDataConstructor
  = PlutusI
  | PlutusB
  | PlutusConstr
  | PlutusList
  | PlutusMap
  deriving stock
    ( -- | @since 1.1.0
      Show,
      -- | @since 1.1.0
      Eq,
      -- | @since 1.1.0
      Ord
    )

-- | @since 1.1.0
data InternalStrategy
  = InternalListStrat
  | InternalPairStrat
  | InternalDataStrat
  | InternalAssocMapStrat
  -- This exists solely so I can get a 'DataEncoding' out of an opaque, it's not really used
  | InternalOpaqueStrat
  deriving stock
    ( -- | @since 1.1.0
      Show,
      -- | @since 1.1.0
      Eq,
      -- | @since 1.1.0
      Ord
    )
