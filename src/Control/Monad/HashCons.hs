{-# LANGUAGE FunctionalDependencies #-}

-- | Module: Control.Monad.HashCons
--
-- Provides a transformer, and a capability type class in the style of @mtl@,
-- for hash consing. See the Covenant wiki for how this works.
module Control.Monad.HashCons
  ( -- * Transformer
    HashConsT,
    runHashConsT,
    hashCons,

    -- * Capability type class
    MonadHashCons (..),
  )
where

import Control.Monad.State.Strict
  ( StateT,
    get,
    modify,
    runStateT,
  )
import Control.Monad.Trans (MonadTrans (lift))
import Control.Monad.Trans.Except (ExceptT)
import Control.Monad.Trans.Maybe (MaybeT)
import Control.Monad.Trans.RWS.CPS (RWST)
import Control.Monad.Trans.Reader (ReaderT)
import Control.Monad.Trans.Writer.CPS (WriterT)
import Data.Bimap (Bimap)
import Data.Bimap qualified as Bimap
import Data.Kind (Type)

-- | A transformer implementing hash consing capabilities, with references of
-- type @r@ and referents of type @e@. It is assumed that values of type @e@
-- contain values of type @r@ in their capacity as references, though this is
-- not a requirement of this transformer.
--
-- @since 1.0.0
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

-- | Execute the computation described, returning both the result and the unique
-- pairings of @r@ and @e@ produced as part of it.
--
-- @since 1.0.0
runHashConsT ::
  forall (r :: Type) (e :: Type) (m :: Type -> Type) (a :: Type).
  HashConsT r e m a ->
  m (a, Bimap r e)
runHashConsT (HashConsT comp) = runStateT comp Bimap.empty

-- | Given a value of type @e@, produce the unique value of type @r@ acting as a
-- reference to it. This @r@ will be cached, ensuring any future requests for
-- the reference for this value of type @e@ will be the same.
--
-- @since 1.0.0
hashCons ::
  forall (r :: Type) (e :: Type) (m :: Type -> Type).
  (Ord r, Ord e, Bounded r, Enum r, Monad m) =>
  e ->
  HashConsT r e m r
hashCons x = HashConsT $ do
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

-- | An @mtl@-style capability type class for hash consing capability, using
-- references of type @r@ and values of type @e@.
--
-- = Laws
--
-- 1. @'refTo' x '>>' 'refTo' x@ @=@ @'refTo' x@
--
-- @since 1.0.0
class
  (Eq e, Eq r, Monad m) =>
  MonadHashCons (r :: Type) (e :: Type) (m :: Type -> Type)
    | m -> e r
  where
  -- | Produce the unique value of type @r@ that acts as a reference for the
  -- given value of type @e@.
  --
  -- @since 1.0.0
  refTo :: e -> m r

-- | @since 1.0.0
instance (Ord r, Ord e, Bounded r, Enum r, Monad m) => MonadHashCons r e (HashConsT r e m) where
  {-# INLINEABLE refTo #-}
  refTo = hashCons

-- | @since 1.0.0
instance (MonadHashCons r e m) => MonadHashCons r e (MaybeT m) where
  {-# INLINEABLE refTo #-}
  refTo e = lift (refTo e)

-- | @since 1.0.0
instance (MonadHashCons r e m) => MonadHashCons r e (ReaderT r' m) where
  {-# INLINEABLE refTo #-}
  refTo e = lift (refTo e)

-- | @since 1.0.0
instance (MonadHashCons r e m) => MonadHashCons r e (StateT s m) where
  {-# INLINEABLE refTo #-}
  refTo e = lift (refTo e)

-- | @since 1.0.0
instance (MonadHashCons r e m) => MonadHashCons r e (WriterT w m) where
  {-# INLINEABLE refTo #-}
  refTo e = lift (refTo e)

-- | @since 1.0.0
instance (MonadHashCons r e m) => MonadHashCons r e (RWST r' w s m) where
  {-# INLINEABLE refTo #-}
  refTo e = lift (refTo e)

-- | @since 1.0.0
instance (MonadHashCons r e m) => MonadHashCons r e (ExceptT e m) where
  {-# INLINEABLE refTo #-}
  refTo e = lift (refTo e)
