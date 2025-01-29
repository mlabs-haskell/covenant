{-# LANGUAGE AllowAmbiguousTypes #-}

-- |
-- Module: Covenant.Expr
-- Copyright: (C) MLabs 2025
-- License: Apache 2.0
-- Maintainer: koz@mlabs.city, farseen@mlabs.city, sean@mlabs.city
--
-- Contains the basic functionality to build up Covenant expressions
-- programmatically.
--
-- @since 1.0.0
module Covenant.Expr
  ( -- * Types
    Id,
    Arg,
    Ref (..),
    PrimCall (..),
    Expr,
    ExprBuilder,
    Scope,
    ExprGraph,

    -- * Functions
    emptyScope,

    -- ** Build up expressions
    lit,
    prim,
    arg,
    app,
    lam,

    -- ** Compile an expression
    toExprGraph,
  )
where

import Algebra.Graph.Acyclic.AdjacencyMap
  ( AdjacencyMap,
    toAcyclic,
    vertex,
  )
import Algebra.Graph.AdjacencyMap qualified as Cyclic
import Control.Monad.State.Strict (runState)
import Covenant.Internal.Expr
  ( Arg (Arg),
    Expr (App, Lam, Lit, Prim),
    ExprBuilder (ExprBuilder),
    Id,
    PrimCall (PrimCallOne, PrimCallSix, PrimCallThree, PrimCallTwo),
    Ref (AnArg, AnId),
    app,
    idOf,
    lit,
    prim,
  )
import Data.Bimap (Bimap)
import Data.Bimap qualified as Bimap
import Data.Maybe (mapMaybe)
import Data.Proxy (Proxy (Proxy))
import GHC.TypeNats (CmpNat, KnownNat, natVal, type (+))
import Numeric.Natural (Natural)

-- | A Covenant program, represented as an acyclic graph.
--
-- @since 1.0.0
data ExprGraph = ExprGraph (Id, Expr) (AdjacencyMap (Id, Expr))
  deriving stock
    ( -- | @since 1.0.0
      Eq,
      -- | @since 1.0.0
      Show
    )

-- | Given an 'Id' result in a builder monad, compile the computation that 'Id'
-- refers to into a call graph. This is guaranteed to be acyclic.
--
-- @since 1.0.0
toExprGraph :: ExprBuilder Id -> Maybe ExprGraph
toExprGraph (ExprBuilder comp) = do
  let (start, binds) = runState comp Bimap.empty
  if Bimap.size binds == 1
    then do
      -- This cannot fail, but the type system can't show it
      initial <- (start,) <$> Bimap.lookup start binds
      pure . ExprGraph initial . vertex $ initial
    else do
      let asGraph = Cyclic.edges . go binds $ start
      -- This cannot fail, but the type system can't show it
      acyclic <- toAcyclic asGraph
      -- Same as above
      initial <- (start,) <$> Bimap.lookup start binds
      pure . ExprGraph initial $ acyclic
  where
    go ::
      Bimap Id Expr ->
      Id ->
      [((Id, Expr), (Id, Expr))]
    go binds curr = case Bimap.lookup curr binds of
      Nothing -> []
      Just e ->
        let idList = toIdList e
            stepdown i = case Bimap.lookup i binds of
              Nothing -> []
              Just e' -> ((curr, e), (i, e')) : go binds i
         in concatMap stepdown idList

-- | A proof of how many arguments are available to a Covenant program. Put
-- another way, a value of type @'Scope' n@ means that we are under @n@ lambdas,
-- each with an argument we can refer to.
--
-- @since 1.0.0
data Scope (n :: Natural) = Scope
  deriving stock
    ( -- | @since 1.0.0
      Eq,
      -- | @since 1.0.0
      Show
    )

-- | Constructs the scopes that proves nothing.
--
-- @since 1.0.0
emptyScope :: Scope 0
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
  forall (n :: Natural) (m :: Natural).
  (KnownNat n, CmpNat n m ~ LT) =>
  Scope m ->
  Arg
arg Scope = Arg . fromIntegral . natVal $ Proxy @n

-- | Given a scope, and a function to construct a lambda body using a \'larger\'
-- scope, construct a lambda with that body.
--
-- For example, this is how you define @id@:
--
-- > lam emptyScope $ \s1 -> pure . AnArg $ arg @0 s1
--
-- This is @const@:
--
-- > lam emptyScope $ \s1 -> lam s1 $ \s2 -> pure . AnArg $ arg @1 s2
--
-- @since 1.0.0
lam ::
  forall (n :: Natural).
  Scope n ->
  (Scope (n + 1) -> ExprBuilder Ref) ->
  ExprBuilder Id
lam Scope f = do
  res <- f Scope
  idOf . Lam $ res

-- Helpers

toIdList :: Expr -> [Id]
toIdList = \case
  Lit _ -> []
  Prim p -> mapMaybe refToId $ case p of
    PrimCallOne _ r -> [r]
    PrimCallTwo _ r1 r2 -> [r1, r2]
    PrimCallThree _ r1 r2 r3 -> [r1, r2, r3]
    PrimCallSix _ r1 r2 r3 r4 r5 r6 -> [r1, r2, r3, r4, r5, r6]
  Lam body -> mapMaybe refToId [body]
  App f x -> mapMaybe refToId [f, x]

refToId :: Ref -> Maybe Id
refToId = \case
  AnArg _ -> Nothing
  AnId i -> Just i
