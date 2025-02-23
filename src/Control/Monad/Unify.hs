{-# LANGUAGE FunctionalDependencies #-}

-- | Module: Control.Monad.Unify
--
-- Unification, in the style of MicroKanren. In this system, /variables/ and
-- /definitions/ (represented by type variables @var@ and @def@ throughout) are
-- allowed to be different types for clarity. Furthermore, we use a CPS-like
-- approach (similar to how 'local' works) to allow it to better integrate with
-- Covenant's other systems.
--
-- = See also
--
-- * [MicroKanren
-- paper](http://webyrd.net/scheme-2013/papers/HemannMuKanren2013.pdf)
module Control.Monad.Unify
  ( UnifyStatus (..),
    UnifyT,
    runUnifyT,
    MonadUnify (..),
  )
where

import Control.Monad (unless)
import Control.Monad.State.Strict (StateT, gets, modify, runStateT)
import Control.Monad.Trans (lift)
import Control.Monad.Trans.Maybe (MaybeT, hoistMaybe, runMaybeT)
import Data.EnumMap.Strict (EnumMap)
import Data.EnumMap.Strict qualified as EnumMap
import Data.Kind (Type)
import Data.Set.NonEmpty (NESet)
import Data.Set.NonEmpty qualified as NESet

-- | @since 1.0.0
data UnifyStatus (var :: Type) (def :: Type)
  = Fresh
  | Equiv (NESet var)
  | Defined def
  deriving stock
    ( -- | @since 1.0.0
      Eq,
      -- | @since 1.0.0
      Show
    )

-- | @since 1.0.0
newtype UnifyT (var :: Type) (def :: Type) (m :: Type -> Type) (a :: Type)
  = UnifyT (StateT (EnumMap var (Either (NESet var) def)) (MaybeT m) a)
  deriving
    ( -- | @since 1.0.0
      Functor,
      -- | @since 1.0.0
      Applicative,
      -- | @since 1.0.0
      Monad
    )
    via StateT (EnumMap var (Either (NESet var) def)) (MaybeT m)

-- | Execute all unifications.
--
-- @since 1.0.0
runUnifyT ::
  forall (var :: Type) (def :: Type) (m :: Type -> Type) (a :: Type).
  (Monad m) =>
  UnifyT var def m a ->
  m (Maybe (a, EnumMap var (Either (NESet var) def)))
runUnifyT (UnifyT comp) = runMaybeT . runStateT comp $ EnumMap.empty

-- | = Laws
--
-- In the description below, @f@ is as follows:
--
-- @
-- f v = case v of
--    'Fresh' -> 'pure' ()
--    'Equiv' vs -> 'unify' v ('Left' ('NESet.findMin' vs))
--    'Defined' x -> 'unify' v ('Right' x)
-- @
--
-- 1. @'status' v '>>' 'status' v@ @=@ @'status' v@
-- 2. @'unify' v x '>>' 'unify' v x@ @=@ @'unify' v x@
-- 3. @'unify' v1 x '>>' 'unify' v2 y@ @=@
--    @'unify' v2 y '>>' 'unify' v1 x@
-- 3. @'unify' v1 ('Left' v2)@ @=@ @'unify' v2 ('Left' v1)@
-- 4. @'status' v '>>=' f@ @=@ @'pure' ()@
--
-- @since 1.0.0
class (Monad m) => MonadUnify var def m | m -> var def where
  -- | @since 1.0.0
  status :: var -> m (UnifyStatus var def)

  -- | @since 1.0.0
  unify :: var -> Either var def -> m ()

-- | @since 1.0.0
instance (Monad m, Enum var, Eq def, Ord var) => MonadUnify var def (UnifyT var def m) where
  {-# INLINEABLE status #-}
  status v =
    UnifyT $ do
      lookedUp <- gets (EnumMap.lookup v)
      pure $ case lookedUp of
        Nothing -> Fresh
        Just (Left vars) -> Equiv vars
        Just (Right x) -> Defined x
  {-# INLINEABLE unify #-}
  unify v x = UnifyT $ do
    lookedUp <- gets (EnumMap.lookup v)
    case lookedUp of
      Nothing -> case x of
        Left v' -> do
          lookedUp' <- gets (EnumMap.lookup v')
          modify $ case lookedUp' of
            Nothing ->
              EnumMap.insert v (Left . NESet.singleton $ v') . EnumMap.insert v' (Left . NESet.singleton $ v)
            Just (Left vars) -> \acc ->
              let newEC = NESet.insert v vars
               in NESet.foldl' (go newEC) acc newEC
            Just (Right def) -> EnumMap.insert v (Right def)
        Right x' -> modify (EnumMap.insert v (Right x'))
      Just (Left vars) -> case x of
        Left v' ->
          let newEC = NESet.insert v' vars
           in modify (\acc -> NESet.foldl' (go newEC) acc newEC)
        Right x' -> modify (\acc -> NESet.foldl' (go2 x') acc vars)
      Just (Right def) -> case x of
        Left v' -> do
          lookedUp' <- gets (EnumMap.lookup v')
          case lookedUp' of
            Nothing -> modify (EnumMap.insert v' (Right def))
            Just (Left vars) ->
              let newEC = NESet.insert v' vars
               in modify (\acc -> NESet.foldl' (go newEC) acc newEC)
            Just (Right def') -> unless (def == def') (lift . hoistMaybe $ Nothing)
        Right x' -> unless (def == x') (lift . hoistMaybe $ Nothing)
    where
      go ::
        NESet var ->
        EnumMap var (Either (NESet var) def) ->
        var ->
        EnumMap var (Either (NESet var) def)
      go newEC acc v' = EnumMap.insert v' (Left newEC) acc
      go2 :: def -> EnumMap var (Either (NESet var) def) -> var -> EnumMap var (Either (NESet var) def)
      go2 x' acc v' = EnumMap.insert v' (Right x') acc
