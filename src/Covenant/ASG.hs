module Covenant.ASG
  ( Id,
    Ref,
    ASGNode,
    CovenantTypeError
      ( BrokenIdReference,
        ForceCompType,
        ForceNonThunk,
        ForceError,
        ThunkValType,
        ThunkError
      ),
    builtin1,
    builtin2,
    builtin3,
    force,
    err,
    lit,
    thunk,
  )
where

import Control.Monad.Except (MonadError (throwError))
import Control.Monad.HashCons (MonadHashCons (refTo))
import Covenant.Constant (AConstant, typeConstant)
import Covenant.Internal.Term
  ( ASGNode (ACompNode, AValNode, AnError),
    ASGNodeType (CompNodeType, ErrorNodeType, ValNodeType),
    CompNodeInfo
      ( Builtin1Internal,
        Builtin2Internal,
        Builtin3Internal,
        ForceInternal
      ),
    CovenantTypeError
      ( BrokenIdReference,
        ForceCompType,
        ForceError,
        ForceNonThunk,
        ThunkError,
        ThunkValType
      ),
    Id,
    Ref,
    ValNodeInfo (LitInternal, ThunkInternal),
    typeId,
    typeRef,
  )
import Covenant.Internal.Type (ValT (ThunkT))
import Covenant.Prim
  ( OneArgFunc,
    ThreeArgFunc,
    TwoArgFunc,
    typeOneArgFunc,
    typeThreeArgFunc,
    typeTwoArgFunc,
  )
import Data.Kind (Type)

-- | @since 1.0.0
builtin1 ::
  forall (m :: Type -> Type).
  (MonadHashCons Id ASGNode m) =>
  OneArgFunc ->
  m Id
builtin1 bi = do
  let node = ACompNode (typeOneArgFunc bi) . Builtin1Internal $ bi
  refTo node

-- | @since 1.0.0
builtin2 ::
  forall (m :: Type -> Type).
  (MonadHashCons Id ASGNode m) =>
  TwoArgFunc ->
  m Id
builtin2 bi = do
  let node = ACompNode (typeTwoArgFunc bi) . Builtin2Internal $ bi
  refTo node

-- | @since 1.0.0
builtin3 ::
  forall (m :: Type -> Type).
  (MonadHashCons Id ASGNode m) =>
  ThreeArgFunc ->
  m Id
builtin3 bi = do
  let node = ACompNode (typeThreeArgFunc bi) . Builtin3Internal $ bi
  refTo node

-- | @since 1.0.0
force ::
  forall (m :: Type -> Type).
  (MonadHashCons Id ASGNode m, MonadError CovenantTypeError m) =>
  Ref ->
  m Id
force r = do
  refT <- typeRef r
  case refT of
    ValNodeType t -> case t of
      ThunkT compT -> refTo . ACompNode compT . ForceInternal $ r
      _ -> throwError . ForceNonThunk $ t
    CompNodeType t -> throwError . ForceCompType $ t
    ErrorNodeType -> throwError ForceError

-- | @since 1.0.0
err ::
  forall (m :: Type -> Type).
  (MonadHashCons Id ASGNode m) =>
  m Id
err = refTo AnError

-- | @since 1.0.0
lit ::
  forall (m :: Type -> Type).
  (MonadHashCons Id ASGNode m) =>
  AConstant ->
  m Id
lit c = refTo . AValNode (typeConstant c) . LitInternal $ c

-- | @since 1.0.0
thunk ::
  forall (m :: Type -> Type).
  (MonadHashCons Id ASGNode m, MonadError CovenantTypeError m) =>
  Id ->
  m Id
thunk i = do
  idT <- typeId i
  case idT of
    CompNodeType t -> refTo . AValNode (ThunkT t) . ThunkInternal $ i
    ValNodeType t -> throwError . ThunkValType $ t
    ErrorNodeType -> throwError ThunkError
