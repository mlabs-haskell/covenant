{-# LANGUAGE TemplateHaskell #-}

module Covenant.Internal.ExprGen
  ( GenDemand (..),
    ExprGenEnv (..),
    ExprGen (..),
    runDemanding,
    satisfyingArg,
  )
where

import Control.Monad.Reader
  ( MonadReader (ask, local),
    ReaderT (ReaderT),
    asks,
    lift,
    runReaderT,
  )
import Covenant.Internal.Arg (Arg (Arg))
import Data.Kind (Type)
import Data.Vector (Vector)
import Data.Vector qualified as Vector
import Optics.Getter (view)
import Optics.TH (makeFieldLabelsNoPrefix)
import Test.QuickCheck (Gen, chooseInt)
import Test.QuickCheck.GenT
  ( MonadGen
      ( choose,
        liftGen,
        resize,
        sized,
        variant
      ),
  )

data GenDemand
  = NoDemand
  | MustBeUnit
  | MustBeBool
  | MustBeInteger
  | MustBeByteString
  | MustBeString
  | MustBePair GenDemand GenDemand
  | MustBeList GenDemand
  | MustBeFunction GenDemand GenDemand
  deriving stock (Eq, Ord, Show)

data ExprGenEnv = ExprGenEnv
  { argsAvailable :: Vector GenDemand,
    currentDemand :: GenDemand
  }
  deriving stock (Eq, Ord, Show)

makeFieldLabelsNoPrefix ''ExprGenEnv

newtype ExprGen (a :: Type) = ExprGen (ReaderT ExprGenEnv Gen a)
  deriving (Functor, Applicative, Monad) via (ReaderT ExprGenEnv Gen)

instance MonadReader ExprGenEnv ExprGen where
  {-# INLINEABLE ask #-}
  ask = ExprGen ask
  {-# INLINEABLE local #-}
  local f (ExprGen comp) = ExprGen $ local f comp

instance MonadGen ExprGen where
  {-# INLINEABLE liftGen #-}
  liftGen g = ExprGen $ lift (liftGen g)
  {-# INLINEABLE variant #-}
  variant n (ExprGen (ReaderT comp)) = ExprGen $ ReaderT $ \env ->
    variant n (comp env)
  {-# INLINEABLE sized #-}
  sized f = ExprGen $ ReaderT $ \env ->
    sized (go env . f)
    where
      go :: forall (a :: Type). ExprGenEnv -> ExprGen a -> Gen a
      go env (ExprGen (ReaderT comp)) = comp env
  {-# INLINEABLE resize #-}
  resize size (ExprGen (ReaderT comp)) = ExprGen $ ReaderT $ \env ->
    resize size (comp env)
  {-# INLINEABLE choose #-}
  choose bounds = ExprGen $ lift (choose bounds)

runDemanding :: forall (a :: Type). GenDemand -> ExprGen a -> Gen a
runDemanding demand (ExprGen comp) = runReaderT comp (ExprGenEnv Vector.empty demand)

-- Gives a random available argument satisfying the current demand, or `Nothing`
-- if no such argument exists.
satisfyingArg :: ExprGen (Maybe Arg)
satisfyingArg = do
  allArgs <- asks (view #argsAvailable)
  currDemand <- asks (view #currentDemand)
  let satisfying = Vector.filter (\(_, demand) -> demand == currDemand) . Vector.indexed $ allArgs
  case Vector.length satisfying of
    0 -> pure Nothing
    len ->
      Just <$> do
        randomIx <- liftGen (chooseInt (0, len - 1))
        pure . Arg . fromIntegral . fst $ satisfying Vector.! randomIx
