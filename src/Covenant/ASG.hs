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
    ASGNode (Lit, Lam, Prim, App, Let, LedgerAccess, LedgerDestruct),
    Scope,
    ASG,
    ASGNeighbourhood,
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
    ledgerAccess,
    ledgerDestruct,

    -- ** Compile
    compileASG,

    -- ** Walking the ASG

    -- *** High-level wrapper
    ASGMove (..),
    ASGMoves (..),
    runASGZipper,
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

import Control.Monad (unless)
import Control.Monad.Action
  ( Action (StateOf, act),
    Actionable,
    MonadUpdate (request, update),
    UpdateT,
    actionable,
    runUpdateT,
  )
import Control.Monad.Error.Class (MonadError, liftEither)
import Control.Monad.HashCons (MonadHashCons (refTo))
import Covenant.Constant (AConstant (ABoolean, AByteString, AData, AList, APair, AString, AUnit, AnInteger))
import Covenant.Internal.ASG
  ( ASG,
    ASGCompileError (ATypeError),
    ASGNeighbourhood,
    ASGZipper,
    TypeError (TyErrAppArgMismatch, TyErrAppNotALambda, TyErrNonHomogenousList, TyErrPrimArgMismatch),
    closeASGZipper,
    compileASG,
    downASGZipper,
    leftASGZipper,
    openASGZipper,
    rightASGZipper,
    upASGZipper,
    viewASGZipper,
  )
import Covenant.Internal.ASGNode
  ( ASGNode
      ( AppInternal,
        LamInternal,
        LedgerAccessInternal,
        LedgerDestructInternal,
        LetInternal,
        LitInternal,
        PrimInternal
      ),
    Arg (Arg),
    Bound (Bound),
    Id,
    PrimCall (PrimCallOne, PrimCallSix, PrimCallThree, PrimCallTwo),
    Ref (ABound, AnArg, AnId),
    TyASGNode (ATyLam),
    TyLam (TyLam),
    typeOfRef,
    pattern App,
    pattern Lam,
    pattern LedgerAccess,
    pattern LedgerDestruct,
    pattern Let,
    pattern Lit,
    pattern Prim,
  )
import Covenant.Internal.PrimType (typeOfOneArgFunc, typeOfSixArgFunc, typeOfThreeArgFunc, typeOfTwoArgFunc)
import Covenant.Internal.TyExpr
  ( TyExpr
      ( TyBoolean,
        TyByteString,
        TyInteger,
        TyList,
        TyPair,
        TyPlutusData,
        TyString,
        TyUnit
      ),
  )
import Covenant.Ledger (LedgerAccessor, LedgerDestructor)
import Covenant.Prim (OneArgFunc, SixArgFunc, ThreeArgFunc, TwoArgFunc)
import Data.Foldable (traverse_)
import Data.Kind (Type)
import Data.Monoid (Endo (Endo))
import Data.Proxy (Proxy (Proxy))
import Data.Vector (Vector)
import Data.Vector qualified as Vector
import GHC.TypeNats (CmpNat, KnownNat, natVal, type (+))
import Numeric.Natural (Natural)

-- | A proof of how many arguments and @let@-binds are available to a Covenant
-- program. Put another way, a value of type @'Scope' n m@ means that we are
-- under @n@ lambdas (each with an argument we can refer to) and @m@ @let@
-- bindings (each with a bound variable we can refer to.
--
-- @since 1.0.0
data Scope (args :: Natural) (lets :: Natural) = Scope (Vector TyASGNode) (Vector TyASGNode)
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
emptyScope = Scope Vector.empty Vector.empty

-- | Construct a literal (constant) value.
--
-- @since 1.0.0
lit ::
  forall (m :: Type -> Type).
  (MonadHashCons Id ASGNode m, MonadError ASGCompileError m) =>
  AConstant -> m Id
lit c = do
  ty <- liftTypeError (typeLit c)
  refTo (LitInternal ty c)

-- | Construct a primitive function call.
--
-- @since 1.0.0
prim ::
  forall (m :: Type -> Type).
  (MonadHashCons Id ASGNode m, MonadError ASGCompileError m) =>
  PrimCall -> m Id
prim p = do
  ty <- typePrim p
  refTo (PrimInternal ty p)

-- | Construct a function application. The first argument is (an expression
-- evaluating to) a function, the second argument is (an expression evaluating
-- to) an argument.
--
-- @since 1.0.0
app ::
  forall (m :: Type -> Type).
  (MonadHashCons Id ASGNode m, MonadError ASGCompileError m) =>
  Ref -> Ref -> m Id
app f x = do
  tyFun <- typeOfRef f
  tyArg <- typeOfRef f
  tyRes <- liftTypeError $ typeApp tyFun tyArg
  refTo (AppInternal tyRes f x)

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

-- | Given the type of the argument and a proof of scope, and a function
-- to construct a lambda body using a \'larger\' proof of scope, construct a
-- lambda with that body.
--
-- Note (Farseen, 2025\/02\/11): Update these examples once parametric polymorphism
-- is implemented.
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
  forall (args :: Natural) (binds :: Natural) (m :: Type -> Type).
  (MonadHashCons Id ASGNode m, MonadError ASGCompileError m) =>
  -- | The type of the lambda argument
  TyASGNode ->
  Scope args binds ->
  (Scope (args + 1) binds -> m Ref) ->
  m Id
lam argTy scope f = do
  let scope' = pushArgToScope argTy scope
  res <- f scope'
  resTy <- typeOfRef res
  let lamTy = TyLam argTy resTy
  refTo (LamInternal lamTy res)

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
  forall (args :: Natural) (binds :: Natural) (m :: Type -> Type).
  (MonadHashCons Id ASGNode m, MonadError ASGCompileError m) =>
  -- | The type of the let binding
  TyASGNode ->
  Scope args binds ->
  Ref ->
  (Scope args (binds + 1) -> m Ref) ->
  m Id
letBind letTy scope r f = do
  let scope' = pushLetToScope letTy scope
  res <- f scope'
  refTo (LetInternal letTy r res)

-- Helpers

pushArgToScope ::
  forall (n :: Natural) (m :: Natural).
  TyASGNode ->
  Scope n m ->
  Scope (n + 1) m
pushArgToScope ty (Scope args lets) =
  Scope (Vector.cons ty args) lets

pushLetToScope ::
  forall (n :: Natural) (m :: Natural).
  TyASGNode ->
  Scope n m ->
  Scope n (m + 1)
pushLetToScope ty (Scope args lets) =
  Scope args (Vector.cons ty lets)

-- Typing Helpers

liftTypeError ::
  (MonadError ASGCompileError m) =>
  Either TypeError a -> m a
liftTypeError = liftEither . mapLeft ATypeError
  where
    mapLeft :: (a -> c) -> Either a b -> Either c b
    mapLeft f (Left x) = Left (f x)
    mapLeft _ (Right x) = Right x

typeLit :: AConstant -> Either TypeError TyExpr
typeLit = \case
  AUnit -> Right TyUnit
  ABoolean _ -> Right TyBoolean
  AnInteger _ -> Right TyInteger
  AByteString _ -> Right TyByteString
  AString _ -> Right TyString
  APair a b -> do
    tyA <- typeLit a
    tyB <- typeLit b
    pure $ TyPair tyA tyB
  AList ty elems -> do
    traverse_
      ( \v1 -> do
          ty' <- typeLit v1
          unless (ty' == ty) (Left TyErrNonHomogenousList)
      )
      elems
    pure $ TyList ty
  AData _ -> pure TyPlutusData

typeApp :: TyASGNode -> TyASGNode -> Either TypeError TyASGNode
typeApp tyFun tyArg = case tyFun of
  ATyLam (TyLam tyParam tyRes) ->
    if tyParam == tyArg
      then Right tyRes
      else Left $ TyErrAppArgMismatch tyParam tyArg
  _ -> Left $ TyErrAppNotALambda tyFun

typePrim ::
  forall (m :: Type -> Type).
  (MonadHashCons Id ASGNode m, MonadError ASGCompileError m) =>
  PrimCall -> m TyASGNode
typePrim p = case p of
  (PrimCallOne fun arg1) -> do
    ty <- typeOfRef arg1
    liftTypeError $ typeOneArgFunc fun ty
  (PrimCallTwo fun arg1 arg2) -> do
    ty1 <- typeOfRef arg1
    ty2 <- typeOfRef arg2
    liftTypeError $ typeTwoArgFunc fun ty1 ty2
  (PrimCallThree fun arg1 arg2 arg3) -> do
    ty1 <- typeOfRef arg1
    ty2 <- typeOfRef arg2
    ty3 <- typeOfRef arg3
    liftTypeError $ typeThreeArgFunc fun ty1 ty2 ty3
  (PrimCallSix fun arg1 arg2 arg3 arg4 arg5 arg6) -> do
    ty1 <- typeOfRef arg1
    ty2 <- typeOfRef arg2
    ty3 <- typeOfRef arg3
    ty4 <- typeOfRef arg4
    ty5 <- typeOfRef arg5
    ty6 <- typeOfRef arg6
    liftTypeError $ typeSixArgFunc fun ty1 ty2 ty3 ty4 ty5 ty6

typeOneArgFunc :: OneArgFunc -> TyASGNode -> Either TypeError TyASGNode
typeOneArgFunc fun tyArg1 =
  let (tyParam1, tyRes) = typeOfOneArgFunc fun
   in if tyParam1 == tyArg1
        then Right tyRes
        else Left $ TyErrPrimArgMismatch (Vector.fromList [tyParam1]) (Vector.fromList [tyArg1])

typeTwoArgFunc :: TwoArgFunc -> TyASGNode -> TyASGNode -> Either TypeError TyASGNode
typeTwoArgFunc fun tyArg1 tyArg2 =
  let (tyParam1, tyParam2, tyRes) = typeOfTwoArgFunc fun
   in if (tyParam1, tyParam2) == (tyArg1, tyArg2)
        then Right tyRes
        else Left $ TyErrPrimArgMismatch (Vector.fromList [tyParam1, tyParam2]) (Vector.fromList [tyArg1, tyArg2])

typeThreeArgFunc :: ThreeArgFunc -> TyASGNode -> TyASGNode -> TyASGNode -> Either TypeError TyASGNode
typeThreeArgFunc fun tyArg1 tyArg2 tyArg3 =
  let (tyParam1, tyParam2, tyParam3, tyRes) = typeOfThreeArgFunc fun
   in if (tyParam1, tyParam2, tyParam3) == (tyArg1, tyArg2, tyArg3)
        then Right tyRes
        else Left $ TyErrPrimArgMismatch (Vector.fromList [tyParam1, tyParam2, tyParam3]) (Vector.fromList [tyArg1, tyArg2, tyArg3])

typeSixArgFunc :: SixArgFunc -> TyASGNode -> TyASGNode -> TyASGNode -> TyASGNode -> TyASGNode -> TyASGNode -> Either TypeError TyASGNode
typeSixArgFunc fun tyArg1 tyArg2 tyArg3 tyArg4 tyArg5 tyArg6 =
  let (tyParam1, tyParam2, tyParam3, tyParam4, tyParam5, tyParam6, tyRes) = typeOfSixArgFunc fun
   in if (tyParam1, tyParam2, tyParam3, tyParam4, tyParam5, tyParam6) == (tyArg1, tyArg2, tyArg3, tyArg4, tyArg5, tyArg6)
        then Right tyRes
        else
          Left $
            TyErrPrimArgMismatch
              (Vector.fromList [tyParam1, tyParam2, tyParam3, tyParam4, tyParam5, tyParam6])
              (Vector.fromList [tyArg1, tyArg2, tyArg3, tyArg4, tyArg5, tyArg6])

-- | Construct a ledger type accessor.
--
-- @since 1.0.0
ledgerAccess ::
  forall (m :: Type -> Type).
  (MonadHashCons Id ASGNode m) =>
  LedgerAccessor ->
  Ref ->
  m Id
ledgerAccess acc = refTo . LedgerAccessInternal acc

-- | Construct a ledger sum type destructor. The first 'Ref' must be a
-- function suitable for destructuring the second 'Ref', though we do not
-- currently check this.
--
-- @since 1.0.0
ledgerDestruct ::
  forall (m :: Type -> Type).
  (MonadHashCons Id ASGNode m) =>
  LedgerDestructor ->
  Ref ->
  Ref ->
  m Id
ledgerDestruct d rFun = refTo . LedgerDestructInternal d rFun

-- ASGZipper

-- | The possible moves in the 'ASGZipper' wrapper monad. These need to be
-- wrapped in 'ASGMoves' to make them usable with the update monad
-- implementation: see 'moveASGView' for a helper avoiding this.
--
-- @since 1.0.0
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

-- | Wrapper needed to make 'ASGMove' a monoid, so that an update monad
-- implementation of traversing the ASG is possible.
--
-- @since 1.0.0
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
  act (ASGMoves moves) = foldMap go moves
    where
      go :: ASGMove -> Endo ASGZipper
      go =
        Endo . \case
          ASGMoveLeft -> leftASGZipper
          ASGMoveRight -> rightASGZipper
          ASGMoveDown -> downASGZipper
          ASGMoveUp -> upASGZipper

-- | Given an 'ASG', open a zipper into it, perform the movements required by
-- the computation, then reclose the zipper at the end. Also produces the moves
-- made as part of the computation.
--
-- @since 1.0.0
runASGZipper ::
  forall (m :: Type -> Type) (a :: Type).
  (Functor m) =>
  UpdateT ASGMoves m a ->
  ASG ->
  m (ASG, ASGMoves, a)
runASGZipper comp =
  fmap (\(z, ms, x) -> (closeASGZipper z, ms, x)) . runUpdateT comp . openASGZipper

-- | Given a direction, attempt to move in that direction. More specifically:
--
-- * 'ASGMoveLeft' attempts to move to the rightmost left sibling of the
-- currently-focused node.
-- * 'ASGMoveRight' attempts to move to the leftmost right sibling of the
-- currently-focused node.
-- * 'ASGMoveDown' moves to the leftmost child of the currently-focused node.
-- * 'ASGMoveUp' moves to the parent of the currently-focused node. If the node
-- has multiple parents, the move is a \'reversal\' of whatever move got us
-- there.
--
-- If a move is impossible, nothing happens.
--
-- = Note
--
-- This mirrors the movement functionality over \'raw\' 'ASGZipper's. See the
-- descriptions of those functions for more precise information.
--
-- @since 1.0.0
moveASGView ::
  forall (m :: Type -> Type).
  (MonadUpdate ASGMoves m) =>
  ASGMove ->
  m ()
moveASGView = update . ASGMoves . actionable

-- | Get the current implicit zipper state.
--
-- @since 1.0.0
currentASGView ::
  forall (m :: Type -> Type).
  (MonadUpdate ASGMoves m) =>
  m ASGZipper
currentASGView = request
