{-# LANGUAGE FunctionalDependencies #-}

module Control.Monad.Unify
  ( UnifyResult (..),
    UnifyT,
    runUnifyT,
    MonadUnify (..),
  )
where

import Control.Monad.Reader (ReaderT, asks, local, runReaderT)
import Data.Kind (Type)
import Data.List.NonEmpty (NonEmpty ((:|)))
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Set.NonEmpty (NESet)
import Data.Set.NonEmpty qualified as NESet
import Test.QuickCheck
  ( CoArbitrary (coarbitrary),
    Function (function),
    functionMap,
    variant,
  )

-- | @since 1.0.0
data UnifyResult (abs :: Type) (conc :: Type)
  = DoesNotUnify abs (Either abs conc)
  | Equivalent
  | UnifiesTo conc
  deriving stock
    ( -- | @since 1.0.0
      Eq,
      -- | @since 1.0.0
      Show
    )

-- | @since 1.0.0
instance (CoArbitrary abs, CoArbitrary conc) => CoArbitrary (UnifyResult abs conc) where
  {-# INLINEABLE coarbitrary #-}
  coarbitrary res = case res of
    DoesNotUnify x y -> variant (0 :: Int) . coarbitrary x . coarbitrary y
    Equivalent -> variant (1 :: Int)
    UnifiesTo x -> variant (2 :: Int) . coarbitrary x

-- | @since 1.0.0
instance (Function abs, Function conc) => Function (UnifyResult abs conc) where
  {-# INLINEABLE function #-}
  function = functionMap into outOf
    where
      into :: UnifyResult abs conc -> Either (abs, Either abs conc) (Maybe conc)
      into = \case
        DoesNotUnify x y -> Left (x, y)
        Equivalent -> Right Nothing
        UnifiesTo x -> Right (Just x)
      outOf :: Either (abs, Either abs conc) (Maybe conc) -> UnifyResult abs conc
      outOf = \case
        Left (x, y) -> DoesNotUnify x y
        Right Nothing -> Equivalent
        Right (Just x) -> UnifiesTo x

newtype UnifyEnv (abs :: Type) (conc :: Type)
  = UnifyEnv (Map abs (Either conc (NESet abs)))
  deriving (Eq) via (Map abs (Either conc (NESet abs)))
  deriving stock (Show)

definedAs ::
  forall (abs :: Type) (conc :: Type).
  (Ord abs) =>
  abs -> UnifyEnv abs conc -> Maybe (Either conc (NESet abs))
definedAs x (UnifyEnv xs) = Map.lookup x xs

addNewEC ::
  forall (abs :: Type) (conc :: Type).
  (Ord abs) =>
  abs -> abs -> UnifyEnv abs conc -> UnifyEnv abs conc
addNewEC x y (UnifyEnv xs) =
  let newEC = NESet.fromList $ x :| [y]
   in UnifyEnv . Map.insert x (Right newEC) . Map.insert y (Right newEC) $ xs

growEC ::
  forall (abs :: Type) (conc :: Type).
  (Ord abs) =>
  abs -> NESet abs -> UnifyEnv abs conc -> UnifyEnv abs conc
growEC extra ec (UnifyEnv xs) = UnifyEnv . NESet.foldl' go xs $ expanded
  where
    expanded :: NESet abs
    expanded = NESet.insert extra ec
    go :: Map abs (Either conc (NESet abs)) -> abs -> Map abs (Either conc (NESet abs))
    go acc x = Map.insert x (Right expanded) acc

define ::
  forall (abs :: Type) (conc :: Type).
  (Ord abs) =>
  abs -> conc -> UnifyEnv abs conc -> UnifyEnv abs conc
define x def (UnifyEnv xs) = UnifyEnv . Map.insert x (Left def) $ xs

unifyECs ::
  forall (abs :: Type) (conc :: Type).
  (Ord abs) =>
  NESet abs -> NESet abs -> UnifyEnv abs conc -> UnifyEnv abs conc
unifyECs ec1 ec2 (UnifyEnv xs) = UnifyEnv . NESet.foldl' go xs $ unified
  where
    unified :: NESet abs
    unified = NESet.union ec1 ec2
    go :: Map abs (Either conc (NESet abs)) -> abs -> Map abs (Either conc (NESet abs))
    go acc x = Map.insert x (Right unified) acc

defineEC ::
  forall (abs :: Type) (conc :: Type).
  (Ord abs) =>
  NESet abs -> conc -> UnifyEnv abs conc -> UnifyEnv abs conc
defineEC ec def (UnifyEnv xs) = UnifyEnv . NESet.foldl' go xs $ ec
  where
    go :: Map abs (Either conc (NESet abs)) -> abs -> Map abs (Either conc (NESet abs))
    go acc x = Map.insert x (Left def) acc

-- | @since 1.0.0
newtype UnifyT (abs :: Type) (conc :: Type) (m :: Type -> Type) (a :: Type)
  = UnifyT (ReaderT (UnifyEnv abs conc) m a)
  deriving
    ( -- | @since 1.0.0
      Functor,
      -- | @since 1.0.0
      Applicative,
      -- | @since 1.0.0
      Monad
    )
    via ReaderT (UnifyEnv abs conc) m

-- | @since 1.0.0
runUnifyT ::
  forall (abs :: Type) (conc :: Type) (m :: Type -> Type) (a :: Type).
  UnifyT abs conc m a ->
  m a
runUnifyT (UnifyT comp) = runReaderT comp . UnifyEnv $ Map.empty

-- | = Laws
--
-- 1. @'unify' x y (\_ -> 'unify' x y f)@ @=@
--    @'unify' x y f@
-- 2. @'unify' v1 ('Left' v2) (\res1 -> unify v2 ('Left' v1) (f res1))@
--    @=@
--    @'unify' v2 ('Left' v1) (\res2 -> unify v1 ('Left' v2) (\res1 -> f res1 res2)@
--
-- @since 1.0.0
class (Monad m, Eq conc) => MonadUnify abs conc m | m -> abs conc where
  unify ::
    forall (a :: Type).
    abs ->
    Either abs conc ->
    (UnifyResult abs conc -> m a) ->
    m a

-- | @since 1.0.0
instance (Eq conc, Ord abs, Monad m) => MonadUnify abs conc (UnifyT abs conc m) where
  {-# INLINEABLE unify #-}
  unify ::
    forall (a :: Type).
    abs ->
    Either abs conc ->
    (UnifyResult abs conc -> UnifyT abs conc m a) ->
    UnifyT abs conc m a
  unify abs1 y f = case y of
    Left abs2 -> do
      defAbs1 <- UnifyT . asks $ definedAs abs1
      defAbs2 <- UnifyT . asks $ definedAs abs2
      case defAbs1 of
        Nothing -> UnifyT $ case defAbs2 of
          Nothing -> local (addNewEC abs1 abs2) (callback Equivalent)
          Just (Left def2) -> local (define abs1 def2) (callback . UnifiesTo $ def2)
          Just (Right ec2) -> local (growEC abs1 ec2) (callback Equivalent)
        Just (Left def1) -> case defAbs2 of
          Nothing -> UnifyT $ local (define abs2 def1) (callback . UnifiesTo $ def1)
          Just (Left def2) -> unifyConcrete def1 def2
          Just (Right ec2) -> UnifyT $ local (defineEC ec2 def1) (callback . UnifiesTo $ def1)
        Just (Right ec1) -> UnifyT $ case defAbs2 of
          Nothing -> local (growEC abs2 ec1) (callback Equivalent)
          Just (Left def2) -> local (defineEC ec1 def2) (callback . UnifiesTo $ def2)
          Just (Right ec2) -> local (unifyECs ec1 ec2) (callback Equivalent)
    Right conc -> handleMixed abs1 conc
    where
      handleMixed :: abs -> conc -> UnifyT abs conc m a
      handleMixed var def =
        (UnifyT . asks $ definedAs var) >>= \case
          Nothing -> UnifyT $ local (define var def) (callback (UnifiesTo def))
          Just (Left def') -> unifyConcrete def def'
          Just (Right ec) -> UnifyT $ local (defineEC ec def) (callback (UnifiesTo def))
      unifyConcrete :: conc -> conc -> UnifyT abs conc m a
      unifyConcrete conc1 conc2 = f (if conc1 == conc2 then UnifiesTo conc1 else DoesNotUnify abs1 y)
      callback :: UnifyResult abs conc -> ReaderT (UnifyEnv abs conc) m a
      callback arg = let UnifyT comp = f arg in comp
