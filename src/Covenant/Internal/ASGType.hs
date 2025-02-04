module Covenant.Internal.ASGType
  ( -- * Types
    ASGType (..),
    TyConstant (..),
    TyPlutusData (..),

    -- * Classes
    HasType (..),
  )
where

-- | The type of an @ASGNode@.
--
-- @since 1.0.0
data ASGType
  = TyConstant TyConstant
  | TyLam ASGType ASGType -- TyLam ArgType ResType
  deriving stock
    ( -- | @since 1.0.0
      Eq,
      -- | @since 1.0.0
      Ord,
      -- | @since 1.0.0
      Show
    )

-- | The type of Plutus constant terms.
--
-- @since 1.0.0
data TyConstant
  = TyUnit
  | TyBoolean
  | TyInteger
  | TyByteString
  | TyString
  | TyPair ASGType ASGType
  | TyList ASGType
  | TyPlutusData TyPlutusData
  deriving stock
    ( -- | @since 1.0.0
      Eq,
      -- | @since 1.0.0
      Ord,
      -- | @since 1.0.0
      Show
    )

-- | The type of @PlutusData@ terms.
--
-- @since 1.0.0
data TyPlutusData
  = TyPlutusConstr -- [TODO]
  | TyPlutusMap TyPlutusData TyPlutusData -- TyPlutusMap Key Value
  | TyPlutusList TyPlutusData
  | TyPlutusI
  | TyPlutusB
  deriving stock
    ( -- | @since 1.0.0
      Eq,
      -- | @since 1.0.0
      Ord,
      -- | @since 1.0.0
      Show
    )

-- | HasType represents anything that has a type.
--
-- @since 1.0.0
class HasType f where
  typeOf :: f -> ASGType
