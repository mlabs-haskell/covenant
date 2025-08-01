module Covenant.Internal.Strategy
  ( DataEncoding (..),
    PlutusDataStrategy (..),
    InternalStrategy (..),
    PlutusDataConstructor (..),
  )
where

-- | Describes how a datatype is represented onchain.
--
-- @since 1.1.0
data DataEncoding
  = -- | The datatype is represented using the SOP primitives.
    --
    -- @since 1.1.0
    SOP
  | -- | The datatype is represented as @Data@, using the
    -- specified strategy to determine specifics.
    --
    -- @since 1.1.0
    PlutusData PlutusDataStrategy
  | -- | The type uses one of the builtin \'special\' strategies. This
    -- is used only for specific types and isn't generally available
    -- for use.
    --
    -- @since 1.1.0
    BuiltinStrategy InternalStrategy
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

-- | Specifics of how a @Data@-encoded datatype is represented.
--
-- @since 1.1.0
data PlutusDataStrategy
  = -- | The type is encoded as an @Integer@, corresponding to which \'arm\'
    -- of the datatype we want.
    --
    -- @since 1.1.0
    EnumData
  | -- | The type is encoded as a list of its fields.
    --
    -- @since 1.1.0
    ProductListData
  | -- | The type is encoded using @Constr@.
    --
    -- @since 1.1.0
    ConstrData
  | -- | The type \'borrows\' the encoding of whatever it wraps.
    --
    -- @since 1.1.0
    NewtypeData
  deriving stock
    ( -- | @since 1.1.0
      Show,
      -- | @since 1.1.0
      Eq,
      -- | @since 1.1.0
      Ord
    )

-- | The constructors of the onchain @Data@ type. Needed for other definitions
-- here.
--
-- @since 1.1.0
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

data InternalStrategy
  = InternalListStrat
  | InternalPairStrat
  | InternalDataStrat
  | InternalAssocMapStrat
  | -- This exists solely so I can get a 'DataEncoding' out of an opaque, it's not really used
    InternalOpaqueStrat
  deriving stock
    ( Show,
      Eq,
      Ord
    )
