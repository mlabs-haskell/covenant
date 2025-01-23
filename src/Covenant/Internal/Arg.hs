module Covenant.Internal.Arg
  ( Arg (..),
  )
where

import Data.Word (Word64)

-- | An argument passed to a function in a Covenant program.
--
-- @since 1.0.0
newtype Arg = Arg Word64
  deriving
    ( -- | @since 1.0.0
      Eq,
      -- | @since 1.0.0
      Ord
    )
    via Word64
  deriving stock
    ( -- | @since 1.0.0
      Show
    )
