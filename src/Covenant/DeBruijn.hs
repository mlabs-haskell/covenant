{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}

-- |
-- Module: Covenant.DeBruijn
-- Copyright: (C) MLabs 2025
-- License: Apache 2.0
-- Maintainer: koz@mlabs.city, sean@mlabs.city
--
-- DeBruijn indexing type and helpers. These are mainly used for scope tracking.
module Covenant.DeBruijn
  ( DeBruijn (Z, S),
    asInt,
  )
where

import Control.Monad (guard)
import Data.Coerce (coerce)
import Data.List.NonEmpty (NonEmpty)
import Data.Semigroup (Semigroup (sconcat, stimes), Sum (Sum))
import Data.Word (Word32)
import Optics.Core (Prism', prism)
import Test.QuickCheck (Arbitrary)

-- | A DeBruijn index.
--
-- @since 1.0.0
newtype DeBruijn = DeBruijn Word32
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

-- | Enables some manner of arithmetic with 'DeBruijn's. In this case, '<>' is
-- analogous to '+', while @'stimes' b@ is analogous to scalar multiplication by
-- @b@. Note that 'DeBruijn's cannot be scaled by negative numbers.
--
-- @since 1.0.0
instance Semigroup DeBruijn where
  {-# INLINEABLE (<>) #-}
  DeBruijn x <> DeBruijn y = DeBruijn (x + y)
  {-# INLINEABLE sconcat #-}
  sconcat = DeBruijn . sum . coerce @(NonEmpty DeBruijn) @(NonEmpty Word32)
  {-# INLINEABLE stimes #-}
  stimes b = DeBruijn . coerce . stimes b . coerce @_ @(Sum Word32)

-- | @since 1.0.0
instance Monoid DeBruijn where
  {-# INLINEABLE mempty #-}
  mempty = Z

-- | The zero index.
--
-- @since 1.0.0
pattern Z :: DeBruijn
pattern Z <- DeBruijn 0
  where
    Z = DeBruijn 0

-- | Successor to an index.
--
-- @since 1.0.0
pattern S :: DeBruijn -> DeBruijn
pattern S x <- (reduce -> Just x)
  where
    S (DeBruijn x) = DeBruijn (x + 1)

{-# COMPLETE Z, S #-}

-- | Construct a DeBruijn from an Int, or deconstruct a Debruijn into an Int
--
-- @since 1.1.0
asInt :: Prism' Int DeBruijn
asInt = prism (\(DeBruijn x) -> fromIntegral x) (\x -> if x >= 0 then Right . DeBruijn $ fromIntegral x else Left x)

-- Helpers
reduce :: DeBruijn -> Maybe DeBruijn
reduce (DeBruijn x) = DeBruijn (x - 1) <$ guard (x > 0)
