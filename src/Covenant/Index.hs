-- | Module: Covenant.Index
--
-- Positional indexes, starting from 0.
module Covenant.Index
  ( Index,
    intIndex,
    ix0,
    ix1,
    ix2,
    ix3,
    ix4,
  )
where

import Data.Bits (toIntegralSized)
import Data.Coerce (coerce)
import Data.List.NonEmpty (NonEmpty)
import Data.Semigroup (Semigroup (sconcat, stimes), Sum (Sum))
import Data.Word (Word32)
import Optics.Prism (Prism', prism)

-- | A positional index, starting from zero.
--
-- @since 1.0.0
newtype Index = Index Word32
  deriving
    ( -- | @since 1.0.0
      Eq,
      -- | @since 1.0.0
      Ord
    )
    via Word32
  deriving stock
    ( -- | @since 1.0.0
      Show
    )

-- | Enables some manner of arithmetic with 'Index'ess. In this case, '<>' is
-- analogous to '+', while @'stimes' b@ is analogous to scalar multiplication by
-- @b@. Note that 'Index'es cannot be scaled by negative numbers.
--
-- @since 1.0.0
instance Semigroup Index where
  {-# INLINEABLE (<>) #-}
  Index x <> Index y = Index (x + y)
  {-# INLINEABLE sconcat #-}
  sconcat = Index . sum . coerce @(NonEmpty Index) @(NonEmpty Word32)
  {-# INLINEABLE stimes #-}
  stimes b = Index . coerce . stimes b . coerce @_ @(Sum Word32)

-- | @since 1.0.0
instance Monoid Index where
  {-# INLINEABLE mempty #-}
  mempty = Index 0

-- | Helper to construct, and convert, 'Index'es and 'Int's. This is needed
-- because unfortunately, the standard Haskell practice is to use 'Int' for
-- indexes.
--
-- To use this, do one of the following:
--
-- * Construct with @'preview'@: for example, @'preview' intIndex 1@.
-- * Destruct with @'review'@.
--
-- @since 1.0.0
intIndex :: Prism' Int Index
intIndex =
  prism
    (fromIntegral . coerce @_ @Word32)
    (\i -> maybe (Left i) (Right . Index) . toIntegralSized $ i)

-- | Helper for the first index.
--
-- @since 1.0.0
ix0 :: Index
ix0 = Index 0

-- | Helper for the second index.
--
-- @since 1.0.0
ix1 :: Index
ix1 = Index 1

-- | Helper for the third index.
--
-- @since 1.0.0
ix2 :: Index
ix2 = Index 2

-- | Helper for the fourth index.
--
-- @since 1.0.0
ix3 :: Index
ix3 = Index 3

-- | Helper for the fifth index.
--
-- @since 1.0.0
ix4 :: Index
ix4 = Index 4
