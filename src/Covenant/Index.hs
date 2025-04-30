{-# LANGUAGE RoleAnnotations #-}

-- |
-- Module: Covenant.Index
-- Copyright: (C) MLabs 2025
-- License: Apache 2.0
-- Maintainer: koz@mlabs.city, sean@mlabs.city
--
-- Positional indexes, starting from 0, and cardinality indicators.
--
-- @since 1.0.0
module Covenant.Index
  ( Index,
    Count,
    intIndex,
    intCount,
    ix0,
    count0,
    ix1,
    count1,
    ix2,
    count2,
    ix3,
    count3,
  )
where

import Data.Bits (toIntegralSized)
import Data.Coerce (coerce)
import Data.List.NonEmpty (NonEmpty)
import Data.Semigroup (Semigroup (sconcat, stimes), Sum (Sum))
import Data.Word (Word32)
import GHC.TypeLits (Symbol)
import Optics.Prism (Prism', prism)
import Test.QuickCheck (Arbitrary)

-- | A positional index, starting from zero. The label allows distinguishing
-- different flavours of indices.
--
-- @since 1.0.0
newtype Index (ofWhat :: Symbol) = Index Word32
  deriving
    ( -- | @since 1.0.0
      Eq,
      -- | @since 1.0.0
      Ord,
      -- | @since 1.0.0
      Arbitrary
    )
    via Word32
  deriving stock
    ( -- | @since 1.0.0
      Show
    )

type role Index nominal

-- | Enables some manner of arithmetic with 'Index'ess. In this case, '<>' is
-- analogous to '+', while @'stimes' b@ is analogous to scalar multiplication by
-- @b@. Note that 'Index'es cannot be scaled by negative numbers.
--
-- @since 1.0.0
instance Semigroup (Index ofWhat) where
  {-# INLINEABLE (<>) #-}
  Index x <> Index y = Index (x + y)
  {-# INLINEABLE sconcat #-}
  sconcat = Index . sum . coerce @(NonEmpty (Index ofWhat)) @(NonEmpty Word32)
  {-# INLINEABLE stimes #-}
  stimes b = Index . coerce . stimes b . coerce @_ @(Sum Word32)

-- | @since 1.0.0
instance Monoid (Index ofWhat) where
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
intIndex :: forall (ofWhat :: Symbol). Prism' Int (Index ofWhat)
intIndex =
  prism
    (fromIntegral . coerce @_ @Word32)
    (\i -> maybe (Left i) (Right . Index) . toIntegralSized $ i)

-- | Helper for the first index.
--
-- @since 1.0.0
ix0 :: forall (ofWhat :: Symbol). Index ofWhat
ix0 = Index 0

-- | Helper for the second index.
--
-- @since 1.0.0
ix1 :: forall (ofWhat :: Symbol). Index ofWhat
ix1 = Index 1

-- | Helper for the third index.
--
-- @since 1.0.0
ix2 :: forall (ofWhat :: Symbol). Index ofWhat
ix2 = Index 2

-- | Helper for the fourth index.
--
-- @since 1.0.0
ix3 :: forall (ofWhat :: Symbol). Index ofWhat
ix3 = Index 3

-- | An indicator of the cardinality of something. Meant to be paired with
-- 'Index' to specify which unique something you mean.
--
-- @since 1.0.0
newtype Count (ofWhat :: Symbol) = Count Word32
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

type role Count nominal

-- | Helper to construct, and convert, 'Count's and 'Int's. This is needed
-- because unfortunately, sizes of things are usually 'Int's in Haskell.
--
-- To use this, do one of the following:
--
-- * Construct with @'preview'@: for example, @'preview' intCount 1@.
-- * Destruct with @'review'@.
--
-- @since 1.0.0
intCount :: forall (ofWhat :: Symbol). Prism' Int (Count ofWhat)
intCount =
  prism
    (fromIntegral . coerce @_ @Word32)
    (\i -> maybe (Left i) (Right . Count) . toIntegralSized $ i)

-- | Helper for a count of zero items.
--
-- @since 1.0.0
count0 :: forall (ofWhat :: Symbol). Count ofWhat
count0 = Count 0

-- | Helper for a count of one item.
--
-- @since 1.0.0
count1 :: forall (ofWhat :: Symbol). Count ofWhat
count1 = Count 1

-- | Helper for a count of two items.
--
-- @since 1.0.0
count2 :: forall (ofWhat :: Symbol). Count ofWhat
count2 = Count 2

-- | Helper for a count of three items.
--
-- @since 1.0.0
count3 :: forall (ofWhat :: Symbol). Count ofWhat
count3 = Count 3
