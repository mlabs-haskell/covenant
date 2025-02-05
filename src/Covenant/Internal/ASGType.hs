module Covenant.Internal.ASGType
  ( -- * Types
    ASGType (..),
    TyConstant (..),
    TypeError (..),

    -- * Classes
    HasType (..),

    -- * Methods
    typeApp,
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
  | TyPair TyConstant TyConstant
  | TyList TyConstant
  | TyPlutusData
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

-- | The errors that come up while resolving types.
--
-- @since 1.0.0
data TypeError
  = TyErrNotALambda ASGType
  | TyErrArgMismatch ASGType ASGType -- expected, received

typeApp :: ASGType -> ASGType -> Either TypeError ASGType
typeApp tyFun tyArg = case tyFun of
  TyLam tyParam tyRes ->
    if tyParam == tyArg
      then Right tyRes
      else Left $ TyErrArgMismatch tyParam tyArg
  _ -> Left $ TyErrNotALambda tyFun
