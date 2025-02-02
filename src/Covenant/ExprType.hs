module Covenant.ExprType
  ( ExprType (..),
    HasType (..),
  )
where

-- | The type of an Expr
--
-- @since 1.0.0
data ExprType
  = ExprTypeNat
  | ExprTypeLam ExprType ExprType
  deriving stock
    ( -- | @since 1.0.0
      Eq,
      -- | @since 1.0.0
      Ord,
      -- | @since 1.0.0
      Show
    )

-- | HasType represents anything that has a type
--
-- @since 1.0.0
class HasType f where
  typeOf :: f -> ExprType
