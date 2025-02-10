{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE PatternSynonyms #-}

-- |
-- Module: Covenant.ASG
-- Copyright: (C) MLabs 2025
-- License: Apache 2.0
-- Maintainer: koz@mlabs.city, farseen@mlabs.city, sean@mlabs.city
--
-- Contains the basic functionality to build up Covenant expressions
-- programmatically.
--
-- Throughout, we will refer to the \'ASG\' in a number of contexts. This stands
-- for \'abstract syntax graph\', which is an AST (abstract syntax tree) with as
-- much sharing of substructure as possible. This makes it a DAG (directed
-- acyclic graph), hence its name change. We achieve this using hash consing:
-- please see the Covenant wiki for more details about how this works.
--
-- @since 1.0.0
module Covenant.ASG
  ( -- * Types
    Id,
    Arg,
    Bound,
    Ref (..),
    PrimCall (..),
    ASGBuilder,
    ASGNode (Lit, Lam, Prim, App, Let),
    Scope,
    ASG,
    ASGZipper,

    -- * Functions

    -- ** Scope construction
    emptyScope,

    -- ** Builder functionality
    lit,
    prim,
    arg,
    bound,
    app,
    lam,
    letBind,

    -- ** Compile
    compileASG,

    -- ** Walking the ASG

    -- *** High-level wrapper
    ASGMove (..),
    ASGMoves (..),
    ASGTraverseT (..),
    runASGTraverseT,
    moveASGView,
    currentASGView,

    -- *** Low-level interface
    openASGZipper,
    closeASGZipper,
    viewASGZipper,
    downASGZipper,
    leftASGZipper,
    rightASGZipper,
    upASGZipper,
  )
where

import Control.Monad.Action
  ( Action (StateOf, act),
    Actionable,
    MonadUpdate (request, update),
    UpdateT,
    actionable,
    runUpdateT,
  )
import Covenant.Internal.ASG
  ( ASG,
    ASGZipper,
    closeASGZipper,
    compileASG,
    downASGZipper,
    leftASGZipper,
    openASGZipper,
    rightASGZipper,
    upASGZipper,
    viewASGZipper,
  )
import Covenant.Internal.ASGBuilder
  ( ASGBuilder,
    app,
    idOf,
    lit,
    prim,
  )
import Covenant.Internal.ASGNode
  ( ASGNode (LamInternal, LetInternal),
    Arg (Arg),
    Bound (Bound),
    Id,
    PrimCall (PrimCallOne, PrimCallSix, PrimCallThree, PrimCallTwo),
    Ref (ABound, AnArg, AnId),
    pattern App,
    pattern Lam,
    pattern Let,
    pattern Lit,
    pattern Prim,
  )
import Data.Foldable (foldl')
import Data.Kind (Type)
import Data.Monoid (Endo (Endo))
import Data.Proxy (Proxy (Proxy))
import GHC.TypeNats (CmpNat, KnownNat, natVal, type (+))
import Numeric.Natural (Natural)

-- | A proof of how many arguments and @let@-binds are available to a Covenant
-- program. Put another way, a value of type @'Scope' n m@ means that we are
-- under @n@ lambdas (each with an argument we can refer to) and @m@ @let@
-- bindings (each with a bound variable we can refer to.
--
-- @since 1.0.0
data Scope (args :: Natural) (lets :: Natural) = Scope
  deriving stock
    ( -- | @since 1.0.0
      Eq,
      -- | @since 1.0.0
      Show
    )

-- | Constructs the 'Scope' that proves nothing.
--
-- @since 1.0.0
emptyScope :: Scope 0 0
emptyScope = Scope

-- | Given a proof of scope, construct one of the arguments in that scope. This
-- requires use of @TypeApplications@ to select which argument you are
-- interested in: argument @0@ is the one from the nearest lambda, argument @1@
-- is the one from the next enclosing lambda, and so on.
--
-- See the documentation for 'lam' for an example of how this function should be
-- used.
--
-- @since 1.0.0
arg ::
  forall (n :: Natural) (m :: Natural) (lets :: Natural).
  (KnownNat n, CmpNat n m ~ LT) =>
  Scope m lets ->
  Arg
arg Scope = Arg . fromIntegral . natVal $ Proxy @n

-- | Given a proof of scope, construct one of the @let@-bound variables in that
-- scope. This requires use of @TypeApplications@ to select which bound variable
-- you are interested in: bound variable @0@ is the one from the nearest @let@,
-- bound variable @1@ is the one from the next enclosing @let@, and so on.
--
-- See the documentation for 'letBind' for an example of how this function
-- should be used.
--
-- @since 1.0.0
bound ::
  forall (n :: Natural) (args :: Natural) (m :: Natural).
  (KnownNat n, CmpNat n m ~ LT) =>
  Scope args m ->
  Bound
bound Scope = Bound . fromIntegral . natVal $ Proxy @n

-- | Given a proof of scope, and a function to construct a lambda body using a
-- \'larger\' proof of scope, construct a lambda with that body.
--
-- For example, this is how you define @id@:
--
-- > lam emptyScope $ \s10 -> pure . AnArg $ arg @0 s10
--
-- This is @const@:
--
-- > lam emptyScope $ \s10 -> AnId <$> lam s10 (\s20 -> pure . AnArg $ arg @1 s20)
--
-- @since 1.0.0
lam ::
  forall (n :: Natural) (m :: Natural).
  Scope n m ->
  (Scope (n + 1) m -> ASGBuilder Ref) ->
  ASGBuilder Id
lam Scope f = do
  res <- f Scope
  idOf . LamInternal $ res

-- | Given a proof of scope, a 'Ref' to an expression to bind to, and a function
-- to construct a @let@-binding body using a \'larger\' proof of scope, construct
-- a @let@ binding with that body.
--
-- For example, if you wanted a local variable binding the result of multiplying
-- 5 by 4, which then gets squared, you would do this:
--
-- > do
-- >     five <- lit 5
-- >     four <- lit 4
-- >     prod <- mul five four
-- >     letBind emptyScope prod $ \s01 ->
-- >          mul (ABound . bound @0 $ s01) (ABound . bound @0 $ s01)
--
-- @since 1.0.0
letBind ::
  forall (n :: Natural) (m :: Natural).
  Scope n m ->
  Ref ->
  (Scope n (m + 1) -> ASGBuilder Ref) ->
  ASGBuilder Id
letBind Scope r f = do
  res <- f Scope
  idOf . LetInternal r $ res

-- | @since 1.0.0
data ASGMove
  = ASGMoveLeft
  | ASGMoveRight
  | ASGMoveUp
  | ASGMoveDown
  deriving stock
    ( -- | @since 1.0.0
      Eq,
      -- | @since 1.0.0
      Show
    )

-- | @since 1.0.0
newtype ASGMoves = ASGMoves (Actionable ASGMove)
  deriving
    ( -- | @since 1.0.0
      Semigroup,
      -- | @since 1.0.0
      Monoid
    )
    via Actionable ASGMove

-- | @since 1.0.0
instance Action ASGMoves where
  type StateOf ASGMoves = ASGZipper
  {-# INLINEABLE act #-}
  act (ASGMoves moves) = Endo $ \s -> foldl' go s moves
    where
      go ::
        ASGZipper -> ASGMove -> ASGZipper
      go oldState = \case
        ASGMoveLeft -> leftASGZipper oldState
        ASGMoveRight -> rightASGZipper oldState
        ASGMoveUp -> upASGZipper oldState
        ASGMoveDown -> downASGZipper oldState

-- | @since 1.0.0
newtype ASGTraverseT (m :: Type -> Type) (a :: Type)
  = ASGTraverseT (UpdateT ASGMoves m a)
  deriving
    ( -- | @since 1.0.0
      Functor,
      -- | @since 1.0.0
      Applicative,
      -- | @since 1.0.0
      Monad,
      -- | @since 1.0.0
      MonadUpdate ASGMoves
    )
    via (UpdateT ASGMoves m)

-- | @since 1.0.0
runASGTraverseT ::
  forall (m :: Type -> Type) (a :: Type).
  (Functor m) =>
  ASGTraverseT m a ->
  ASG ->
  m (ASG, ASGMoves, a)
runASGTraverseT (ASGTraverseT comp) =
  fmap (\(z, ms, x) -> (closeASGZipper z, ms, x)) . runUpdateT comp . openASGZipper

-- | @since 1.0.0
moveASGView ::
  forall (m :: Type -> Type).
  (Monad m) =>
  ASGMove ->
  ASGTraverseT m ()
moveASGView = update . ASGMoves . actionable

-- | @since 1.0.0
currentASGView ::
  forall (m :: Type -> Type).
  (Monad m) =>
  ASGTraverseT m ASGZipper
currentASGView = request
