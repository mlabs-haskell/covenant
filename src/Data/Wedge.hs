module Data.Wedge
  ( Wedge (..),
  )
where

-- | @since 1.0.0
data Wedge (a :: Type) (b :: Type)
  = Nowhere
  | Here a
  | There b
  deriving stock
    ( -- | @since 1.0.0
      Eq,
      -- | @since 1.0.0
      Show
    )
