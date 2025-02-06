{-# LANGUAGE AllowAmbiguousTypes #-}

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
    ASGNode,
    ASGBuilder,
    Scope,
    ASG,

    -- * Functions
    emptyScope,

    -- ** Build up expressions
    lit,
    prim,
    arg,
    bound,
    app,
    lam,
    letBind,

    -- ** Compile an expression
    toASG,
  )
where

import Algebra.Graph.Acyclic.AdjacencyMap
  ( AdjacencyMap,
    toAcyclic,
    vertex,
  )
import Algebra.Graph.AdjacencyMap qualified as Cyclic
import Covenant.Internal.ASGBuilder
  ( ASGBuilder,
    ASGBuilderError,
    ASGBuilderState (ASGBuilderState),
    app,
    idOf,
    lit,
    prim,
    runASGBuilder,
  )
import Covenant.Internal.ASGNode
  ( ASGNode (App, Lam, Let, Lit, Prim),
    ASGType (TyLam),
    Arg (Arg),
    Bound (Bound),
    Id,
    PrimCall (PrimCallOne, PrimCallSix, PrimCallThree, PrimCallTwo),
    Ref (ABound, AnArg, AnId),
    typeOfRef,
  )
import Data.Bimap (Bimap)
import Data.Bimap qualified as Bimap
import Data.Maybe (fromJust, mapMaybe)
import Data.Proxy (Proxy (Proxy))
import Data.Vector (Vector)
import Data.Vector qualified as Vector
import GHC.TypeNats (CmpNat, KnownNat, natVal, type (+))
import Numeric.Natural (Natural)

-- | A Covenant program, represented as an acyclic graph.
--
-- @since 1.0.0
data ASG = ASG (Id, ASGNode) (AdjacencyMap (Id, ASGNode))
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
toASG :: ASGBuilder Id -> Either ASGBuilderError ASG
toASG comp = do
  let (startOrError, ASGBuilderState (binds :: Bimap Id ASGNode)) = runASGBuilder comp (ASGBuilderState Bimap.empty)
  start :: Id <- startOrError
  if Bimap.size binds == 1
    then do
      let -- This cannot fail, but the type system can't show it
          initial = (start,) ((Bimap.!) binds start)
      pure . ASG initial . vertex $ initial
    else do
      let asGraph = Cyclic.edges . go binds $ start
          -- This cannot fail, but the type system can't show it
          acyclic = fromJust $ toAcyclic asGraph
          -- Same as above
          initial = (start,) ((Bimap.!) binds start)
      pure . ASG initial $ acyclic
  where
    go ::
      Bimap Id ASGNode ->
      Id ->
      [((Id, ASGNode), (Id, ASGNode))]
    go binds curr = case Bimap.lookup curr binds of
      Nothing -> []
      Just e ->
        let idList = toIdList e
            stepdown i = case Bimap.lookup i binds of
              Nothing -> []
              Just e' -> ((curr, e), (i, e')) : go binds i
         in concatMap stepdown idList

-- | A proof of how many arguments and @let@-binds are available to a Covenant
-- program. Put another way, a value of type @'Scope' n m@ means that we are
-- under @n@ lambdas (each with an argument we can refer to) and @m@ @let@
-- bindings (each with a bound variable we can refer to.
--
-- @since 1.0.0
data Scope (args :: Natural) (lets :: Natural) = Scope (Vector ASGType) (Vector ASGType)
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
emptyScope = Scope (Vector.empty) (Vector.empty)

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
arg (Scope args _) =
  let n = natVal $ Proxy @n
      -- This cannot fail, but the type system can't show it
      argTy = (Vector.!) args (fromIntegral n)
   in Arg (fromIntegral n) argTy

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
bound (Scope _ lets) =
  let n = natVal $ Proxy @n
      -- This cannot fail, but the type system can't show it
      letTy = (Vector.!) lets (fromIntegral n)
   in Bound (fromIntegral n) letTy

-- | Given a proof of scope, and a function to construct a lambda body using a
-- \'larger\' proof of scope, construct a lambda with that body.
--
-- For example, this is how you define @id@:
--
-- > lam emptyScope $ \s10 -> pure . AnArg $ arg @0 s10
--
-- This is @const@:
--
-- > lam emptyScope $ \s10 -> lam s10 $ \s20 -> pure . AnArg $ arg @1 s20
--
-- @since 1.0.0
lam ::
  forall (n :: Natural) (m :: Natural).
  ASGType ->
  Scope n m ->
  (Scope (n + 1) m -> ASGBuilder Ref) ->
  ASGBuilder Id
lam argTy scope f = do
  let scope' = pushArgToScope argTy scope
  res <- f scope'
  let resTy = typeOfRef res
      lamTy = TyLam argTy resTy
  idOf lamTy . Lam $ res

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
  ASGType ->
  Scope n m ->
  Ref ->
  (Scope n (m + 1) -> ASGBuilder Ref) ->
  ASGBuilder Id
letBind letTy scope r f = do
  let scope' = pushLetToScope letTy scope
  res <- f scope'
  idOf letTy . Let r $ res

-- Helpers

pushArgToScope ::
  forall (n :: Natural) (m :: Natural).
  ASGType ->
  Scope n m ->
  Scope (n + 1) m
pushArgToScope ty (Scope args lets) =
  Scope (Vector.cons ty args) lets

pushLetToScope ::
  forall (n :: Natural) (m :: Natural).
  ASGType ->
  Scope n m ->
  Scope n (m + 1)
pushLetToScope ty (Scope args lets) =
  Scope args (Vector.cons ty lets)

toIdList :: ASGNode -> [Id]
toIdList = \case
  Lit _ -> []
  Prim p -> mapMaybe refToId $ case p of
    PrimCallOne _ r -> [r]
    PrimCallTwo _ r1 r2 -> [r1, r2]
    PrimCallThree _ r1 r2 r3 -> [r1, r2, r3]
    PrimCallSix _ r1 r2 r3 r4 r5 r6 -> [r1, r2, r3, r4, r5, r6]
  Lam body -> mapMaybe refToId [body]
  Let x body -> mapMaybe refToId [x, body]
  App f x -> mapMaybe refToId [f, x]

refToId :: Ref -> Maybe Id
refToId = \case
  AnArg _ -> Nothing
  AnId i -> Just i
  ABound _ -> Nothing
