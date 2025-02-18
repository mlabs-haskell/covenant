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

-- | The outcome of a unification attempt.
--
-- @since 1.0.0
data UnifyResult (var :: Type) (def :: Type)
  = -- | Unable to unify the given arguments
    DoesNotUnify var (Either var def)
  | -- | The arguments belong to the same equivalence class
    Equivalent
  | -- | The argument unify to a definition, which is given
    UnifiesTo def
  deriving stock
    ( -- | @since 1.0.0
      Eq,
      -- | @since 1.0.0
      Show
    )

-- | @since 1.0.0
instance (CoArbitrary var, CoArbitrary def) => CoArbitrary (UnifyResult var def) where
  {-# INLINEABLE coarbitrary #-}
  coarbitrary res = case res of
    DoesNotUnify x y -> variant (0 :: Int) . coarbitrary x . coarbitrary y
    Equivalent -> variant (1 :: Int)
    UnifiesTo x -> variant (2 :: Int) . coarbitrary x

-- | @since 1.0.0
instance (Function var, Function def) => Function (UnifyResult var def) where
  {-# INLINEABLE function #-}
  function = functionMap into outOf
    where
      into :: UnifyResult var def -> Either (var, Either var def) (Maybe def)
      into = \case
        DoesNotUnify x y -> Left (x, y)
        Equivalent -> Right Nothing
        UnifiesTo x -> Right (Just x)
      outOf :: Either (var, Either var def) (Maybe def) -> UnifyResult var def
      outOf = \case
        Left (x, y) -> DoesNotUnify x y
        Right Nothing -> Equivalent
        Right (Just x) -> UnifiesTo x

-- | An implementation of MicroKanren-like unification as a concrete monadic
-- stack.
--
-- @since 1.0.0
newtype UnifyT (var :: Type) (def :: Type) (m :: Type -> Type) (a :: Type)
  = UnifyT (ReaderT (UnifyEnv var def) m a)
  deriving
    ( -- | @since 1.0.0
      Functor,
      -- | @since 1.0.0
      Applicative,
      -- | @since 1.0.0
      Monad
    )
    via ReaderT (UnifyEnv var def) m

-- | Execute all unifications.
--
-- @since 1.0.0
runUnifyT ::
  forall (var :: Type) (def :: Type) (m :: Type -> Type) (a :: Type).
  UnifyT var def m a ->
  m a
runUnifyT (UnifyT comp) = runReaderT comp . UnifyEnv $ Map.empty

-- | A capability type class specifying that a stack can perform
-- MicroKanren-style unification.
--
-- = Laws
--
-- 1. @'unify' x y (\_ -> 'unify' x y f)@ @=@
--    @'unify' x y f@
-- 2. @'unify' v1 ('Left' v2) (\res1 -> unify v2 ('Left' v1) (f res1))@
--    @=@
--    @'unify' v2 ('Left' v1) (\res2 -> unify v1 ('Left' v2) (\res1 -> f res1 res2)@
--
-- @since 1.0.0
class (Monad m) => MonadUnify var def m | m -> var def where
  -- | Given a variable, and either a variable or definition, assert that the
  -- these two arguments belong to the same equivalence class. Then, call the
  -- third argument with the outcome of that assertion; the computation inside
  -- the callback argument will note the outcome of this assertion if either, or
  -- both, arguments were fresh. If unification fails, the environment does not
  -- change.
  --
  -- @since 1.0.0
  unify ::
    forall (a :: Type).
    var ->
    Either var def ->
    (UnifyResult var def -> m a) ->
    m a

-- | @since 1.0.0
instance (Eq def, Ord var, Monad m) => MonadUnify var def (UnifyT var def m) where
  {-# INLINEABLE unify #-}
  unify ::
    forall (a :: Type).
    var ->
    Either var def ->
    (UnifyResult var def -> UnifyT var def m a) ->
    UnifyT var def m a
  unify var1 y f = case y of
    Left var2 -> do
      defAbs1 <- UnifyT . asks $ definedAs var1
      defAbs2 <- UnifyT . asks $ definedAs var2
      case defAbs1 of
        Nothing -> UnifyT $ case defAbs2 of
          Nothing -> local (addNewEC var1 var2) (callback Equivalent)
          Just (Left def2) -> local (define var1 def2) (callback . UnifiesTo $ def2)
          Just (Right ec2) -> local (growEC var1 ec2) (callback Equivalent)
        Just (Left def1) -> case defAbs2 of
          Nothing -> UnifyT $ local (define var2 def1) (callback . UnifiesTo $ def1)
          Just (Left def2) -> unifyConcrete def1 def2
          Just (Right ec2) -> UnifyT $ local (defineEC ec2 def1) (callback . UnifiesTo $ def1)
        Just (Right ec1) -> UnifyT $ case defAbs2 of
          Nothing -> local (growEC var2 ec1) (callback Equivalent)
          Just (Left def2) -> local (defineEC ec1 def2) (callback . UnifiesTo $ def2)
          Just (Right ec2) -> local (unifyECs ec1 ec2) (callback Equivalent)
    Right def -> handleMixed var1 def
    where
      handleMixed :: var -> def -> UnifyT var def m a
      handleMixed var def =
        (UnifyT . asks $ definedAs var) >>= \case
          Nothing -> UnifyT $ local (define var def) (callback (UnifiesTo def))
          Just (Left def') -> unifyConcrete def def'
          Just (Right ec) -> UnifyT $ local (defineEC ec def) (callback (UnifiesTo def))
      unifyConcrete :: def -> def -> UnifyT var def m a
      unifyConcrete def1 def2 = f (if def1 == def2 then UnifiesTo def1 else DoesNotUnify var1 y)
      callback :: UnifyResult var def -> ReaderT (UnifyEnv var def) m a
      callback arg = let UnifyT comp = f arg in comp

-- Helpers

-- Internal unification state, which connects a variable to either a concrete
-- definition, or to an equivalence class of other variables whose definition
-- doesn't (yet) exist.
newtype UnifyEnv (var :: Type) (def :: Type)
  = UnifyEnv (Map var (Either def (NESet var)))
  deriving (Eq) via (Map var (Either def (NESet var)))
  deriving stock (Show)

-- Helper for querying the state of a variable. It can either be fresh
-- (`Nothing`), bound to a definition (`Just . Left`) or part of an equivalence
-- class without a definition (`Just . Right`).
definedAs ::
  forall (abs :: Type) (conc :: Type).
  (Ord abs) =>
  abs -> UnifyEnv abs conc -> Maybe (Either conc (NESet abs))
definedAs x (UnifyEnv xs) = Map.lookup x xs

-- Given two fresh variables, construct a new equivalence class consisting of
-- just them, and augment the environment with them.
addNewEC ::
  forall (var :: Type) (def :: Type).
  (Ord var) =>
  var -> var -> UnifyEnv var def -> UnifyEnv var def
addNewEC x y (UnifyEnv xs) =
  let newEC = NESet.fromList $ x :| [y]
   in UnifyEnv . Map.insert x (Right newEC) . Map.insert y (Right newEC) $ xs

-- Given a fresh variable and an already-existing equivalence class, expand that
-- equivalence class with the variable in the environment.
growEC ::
  forall (var :: Type) (def :: Type).
  (Ord var) =>
  var -> NESet var -> UnifyEnv var def -> UnifyEnv var def
growEC extra ec (UnifyEnv xs) = UnifyEnv . NESet.foldl' go xs $ expanded
  where
    expanded :: NESet var
    expanded = NESet.insert extra ec
    go :: Map var (Either def (NESet var)) -> var -> Map var (Either def (NESet var))
    go acc x = Map.insert x (Right expanded) acc

-- Given a variable (which may or may not be fresh) and a definition, place that
-- variable into the equivalence class of that definition in the environment.
define ::
  forall (var :: Type) (def :: Type).
  (Ord var) =>
  var -> def -> UnifyEnv var def -> UnifyEnv var def
define x def (UnifyEnv xs) = UnifyEnv . Map.insert x (Left def) $ xs

-- Given two already-existing equivalence classes, combine them into one
-- equivalence class in the environment.
unifyECs ::
  forall (var :: Type) (def :: Type).
  (Ord var) =>
  NESet var -> NESet var -> UnifyEnv var def -> UnifyEnv var def
unifyECs ec1 ec2 (UnifyEnv xs) = UnifyEnv . NESet.foldl' go xs $ unified
  where
    unified :: NESet var
    unified = NESet.union ec1 ec2
    go :: Map var (Either def (NESet var)) -> var -> Map var (Either def (NESet var))
    go acc x = Map.insert x (Right unified) acc

-- Given an already-existing equivalence class (without a definition), and a
-- desired definition without an equivalence class in the environment, define
-- that equivalence class to now be that of the given definition in the
-- environment.
defineEC ::
  forall (var :: Type) (def :: Type).
  (Ord var) =>
  NESet var -> def -> UnifyEnv var def -> UnifyEnv var def
defineEC ec def (UnifyEnv xs) = UnifyEnv . NESet.foldl' go xs $ ec
  where
    go :: Map var (Either def (NESet var)) -> var -> Map var (Either def (NESet var))
    go acc x = Map.insert x (Left def) acc
