{-# LANGUAGE FunctionalDependencies #-}

-- | Module: Control.Monad.Action
--
-- Monoid actions, and the update monad, as well as an @mtl@-style capability
-- type class.
--
-- = A note on functional dependencies
--
-- To ensure easy inference, we make use of functional dependencies (either
-- directly or by an equivalent mechanism on associated type families) on both
-- the 'Action' and 'MonadUpdate' type classes. Specifically, we insist that:
--
-- 1. Any monoidal action determines the state it acts on; and
-- 2. Any particular stack that implements 'MonadUpdate' determines what its
-- action is.
--
-- This means that any given action can act on _exactly_ one state, and that any
-- given stack has at most one state we can act upon. The second restriction
-- above is in line with the other similar @mtl@-style capability type classes
-- (such as @MonadReader@, @MonadState@ etc), while the first is a reasonable
-- choice given that we want to have both good inference and also the ability
-- for different actions to act on the same state. Given that actions are likely
-- to be fairly application-specific, we don't see this as a significant
-- limitation.
module Control.Monad.Action
  ( -- * Monoid actions

    -- ** Class
    Action (..),

    -- ** Wrapper
    Actionable,
    actionable,

    -- * Action monad

    -- ** Transformer
    UpdateT (..),
    runUpdateT,

    -- ** Capability type class
    MonadUpdate (..),
  )
where

import Acc (Acc)
import Control.Monad.Trans (MonadTrans (lift))
import Data.Functor (void)
import Data.Kind (Type)
import Data.Monoid (Endo, appEndo)

-- | Describes (left) [monoidal actions on a
-- set](https://en.wikipedia.org/wiki/Semigroup_action). In this case, the type
-- @StateOf a@ is \'the state being acted on\' (or \'the state\'), while @a@ is
-- \'the thing doing the acting\' (or \'the action\').
--
-- = Laws
--
-- Briefly, any instance of @'Action' a@ defines a [monoid
-- homomorphism](https://en.wikipedia.org/wiki/Monoid#Monoid_homomorphisms)
-- between @a@ and @'Endo' (StateOf a)@ (which is essentially @StateOf a ->
-- StateOf a)@. In Haskell terms, this means the following laws must hold:
--
-- 1. @'act' 'mempty'@ @=@ @'mempty'@
-- 2. @'act' x '<>' 'act' y@ @=@ @'act' (x '<>' y)@
--
-- @since 1.0.0
class (Monoid a) => Action (a :: Type) where
  type StateOf a :: Type
  act :: a -> Endo (StateOf a)

-- | Often, we want to take a type that doesn't (naturally) form a 'Monoid' and
-- use it as an action. This can be done using a range of \'free monoid
-- constructions\', including lists. However, these aren't optimal due to the
-- append-heavy (and concatenation-heavy) workloads we typically need from
-- actions.
--
-- 'Actionable' is such a \'free monoid construction\' which \'promotes\' any
-- @a@ into a 'Semigroup' and a 'Monoid'. It is fairly opaque, providing only
-- the instances we really need, but it's designed for efficient appending and
-- concatenation.
--
-- To use 'Actionable', you want to do something like this:
--
-- @
-- data MyState = ...
--
-- data MyType = ...
--
-- newtype MyAction = MyAction (Actionable MyType)
--  deriving (Semigroup, Monoid) via (Actionable MyType)
--
-- instance Action MyAction where
--    type StateOf MyAction = MyState
--    act (MyAction acts) = foldMap go acts
--    where
--      go :: MyType -> Endo MyState
--      go x = Endo $ \oldState -> ...
-- @
--
-- To \'inject\' your type into an 'Actionable', use 'actionable'.
--
-- @since 1.0.0
newtype Actionable a = Actionable (Acc a)
  deriving
    ( -- | @since 1.0.0
      Semigroup,
      -- | @since 1.0.0
      Monoid
    )
    via Acc a
  deriving
    ( -- | @since 1.0.0
      Foldable
    )
    via Acc

-- | Wrap a value into an 'Actionable'.
--
-- @since 1.0.0
actionable :: a -> Actionable a
actionable = Actionable . pure

-- | A transformer implementing the \'update monad\' pattern, as described
-- [here](https://www.schoolofhaskell.com/user/edwardk/heap-of-successes).
--
-- We leave the state implicit, as it is uniquely determined by the @act@ type,
-- together with the 'Action' type class requirement.
--
-- = Important note
--
-- This implementation is not suitable for any @m@ that throws exceptions. This
-- includes @IO@, @ST@ and anything stacked atop them. For the reasons why, see
-- [here](https://github.com/haskell-effectful/effectful/blob/master/transformers.md#statet).
--
-- @since 1.0.0
newtype UpdateT (act :: Type) (m :: Type -> Type) (a :: Type)
  = UpdateT (StateOf act -> m (act, a))
  deriving stock
    ( -- | @since 1.0.0
      Functor
    )

-- | @since 1.0.0
instance (Action act, Monad m) => Applicative (UpdateT act m) where
  {-# INLINEABLE pure #-}
  pure x = UpdateT $ \_ -> pure (mempty, x)
  {-# INLINEABLE (<*>) #-}
  UpdateT fs <*> UpdateT xs = UpdateT $ \s -> do
    (act1, f) <- fs s
    let s' = appEndo (act act1) s
    (act2, x) <- xs s'
    pure (act1 <> act2, f x)

-- | @since 1.0.0
instance (Action act, Monad m) => Monad (UpdateT act m) where
  {-# INLINEABLE (>>=) #-}
  UpdateT xs >>= f = UpdateT $ \s -> do
    (act1, x) <- xs s
    let s' = appEndo (act act1) s
    let (UpdateT applied) = f x
    (act2, y) <- applied s'
    pure (act1 <> act2, y)

-- | @since 1.0.0
instance (Action act) => MonadTrans (UpdateT act) where
  {-# INLINEABLE lift #-}
  lift comp = UpdateT $ \_ -> (mempty,) <$> comp

-- | As 'runUpdate', except that it produces the results in the \'inner monad\'
-- of 'UpdateT'.
--
-- @since 1.0.0
runUpdateT ::
  forall (act :: Type) (m :: Type -> Type) (a :: Type).
  (Functor m, Action act) =>
  UpdateT act m a ->
  StateOf act ->
  m (StateOf act, act, a)
runUpdateT (UpdateT comp) s =
  (\(act1, res) -> (appEndo (act act1) s, act1, res)) <$> comp s

-- | An @mtl@-style capability type class describing update monads in general,
-- irrespective of their states and/or actions.
--
-- = Laws
--
-- 1. @'send' x 'Control.Applicative.*>' 'send' y@ @=@ @'send' (x '<>' y)@
--
-- If you define 'update' or 'request', ensure the following also hold:
--
-- 2. @'update' 'mempty'@ @=@ @'pure' ()@
-- 3. @'request' 'Control.Applicative.*>' 'request'@ @=@ @'request'@
-- 4. @'update'@ @=@ @'void' '.' 'send'@
-- 5. @'request'@ @=@ @'send' 'mempty'@
--
-- Laws 4 and 5 form the default definitions of 'update' and 'request'
-- respectively, which obey all these laws.
--
-- @since 1.0.0
class (Action act, Monad m) => MonadUpdate act m | m -> act where
  -- | Performs the given action on the state, returning the result.
  --
  -- @since 1.0.0
  send :: act -> m (StateOf act)

  -- | Performs the given action, returning nothing.
  --
  -- @since 1.0.0
  {-# INLINEABLE update #-}
  update :: act -> m ()
  update = void . send

  -- | Retrieves the state without doing anything to it.
  --
  -- @since 1.0.0
  {-# INLINEABLE request #-}
  request :: m (StateOf act)
  request = send (mempty :: act)

  {-# MINIMAL send #-}

-- | @since 1.0.0
instance (Action act, Monad m) => MonadUpdate act (UpdateT act m) where
  {-# INLINEABLE send #-}
  send x = UpdateT $ \s -> pure (x, appEndo (act x) s)
