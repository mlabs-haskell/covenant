{-# LANGUAGE FunctionalDependencies #-}

module Control.Monad.HashCons
  ( HashCons,
    runHashCons,
    hashCons,
    HashConsT,
    runHashConsT,
    hashConsT,
    MonadHashCons (..),
  )
where

import Control.Monad.State.Strict
  ( State,
    StateT,
    get,
    modify,
    runState,
    runStateT,
  )
import Control.Monad.Trans (MonadTrans)
import Data.Bimap (Bimap)
import Data.Bimap qualified as Bimap
import Data.Kind (Type)

-- | @since 1.0.0
newtype HashCons (r :: Type) (e :: Type) (a :: Type)
  = HashCons (State (Bimap r e) a)
  deriving
    ( -- | @since 1.0.0
      Functor,
      -- | @since 1.0.0
      Applicative,
      -- | @since 1.0.0
      Monad
    )
    via (State (Bimap r e))

-- | @since 1.0.0
runHashCons ::
  forall (r :: Type) (e :: Type) (a :: Type).
  HashCons r e a ->
  (a, Bimap r e)
runHashCons (HashCons comp) = runState comp Bimap.empty

-- | @since 1.0.0
hashCons ::
  forall (r :: Type) (e :: Type).
  (Ord r, Ord e, Bounded r, Enum r) =>
  e ->
  HashCons r e r
hashCons x = HashCons $ do
  binds <- get
  case Bimap.lookupR x binds of
    Nothing ->
      if Bimap.null binds
        then minBound <$ modify (Bimap.insert minBound x)
        else do
          let largestOldRef = fst . Bimap.findMax $ binds
          let newRef = succ largestOldRef
          newRef <$ modify (Bimap.insert newRef x)
    Just ref -> pure ref

-- | @since 1.0.0
newtype HashConsT (r :: Type) (e :: Type) (m :: Type -> Type) (a :: Type)
  = HashConsT (StateT (Bimap r e) m a)
  deriving
    ( -- | @since 1.0.0
      Functor,
      -- | @since 1.0.0
      Applicative,
      -- | @since 1.0.0
      Monad
    )
    via (StateT (Bimap r e) m)
  deriving
    ( -- | @since 1.0.0
      MonadTrans
    )
    via StateT (Bimap r e)

-- | @since 1.0.0
runHashConsT ::
  forall (r :: Type) (e :: Type) (m :: Type -> Type) (a :: Type).
  HashConsT r e m a ->
  m (a, Bimap r e)
runHashConsT (HashConsT comp) = runStateT comp Bimap.empty

-- | @since 1.0.0
hashConsT ::
  forall (r :: Type) (e :: Type) (m :: Type -> Type).
  (Ord r, Ord e, Bounded r, Enum r, Monad m) =>
  e ->
  HashConsT r e m r
hashConsT x = HashConsT $ do
  binds <- get
  case Bimap.lookupR x binds of
    Nothing ->
      if Bimap.null binds
        then minBound <$ modify (Bimap.insert minBound x)
        else do
          let largestOldRef = fst . Bimap.findMax $ binds
          let newRef = succ largestOldRef
          newRef <$ modify (Bimap.insert newRef x)
    Just ref -> pure ref

-- | @since 1.0.0
class
  (Eq e, Eq r, Monad m) =>
  MonadHashCons (r :: Type) (e :: Type) (m :: Type -> Type)
    | m -> e r
  where
  -- | @since 1.0.0
  refTo :: e -> m r

-- | @since 1.0.0
instance (Ord r, Ord e, Bounded r, Enum r) => MonadHashCons r e (HashCons r e) where
  {-# INLINEABLE refTo #-}
  refTo = hashCons

-- | @since 1.0.0
instance (Ord r, Ord e, Bounded r, Enum r, Monad m) => MonadHashCons r e (HashConsT r e m) where
  {-# INLINEABLE refTo #-}
  refTo = hashConsT
