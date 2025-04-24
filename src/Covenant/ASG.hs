module Covenant.ASG
  ( ScopeInfo,
    Id,
    Ref,
    Arg,
    ASGNode,
    ASG,
    rootNode,
    nodeAt,
    CovenantTypeError
      ( BrokenIdReference,
        ForceCompType,
        ForceNonThunk,
        ForceError,
        ThunkValType,
        ThunkError,
        ApplyToValType,
        ApplyToError,
        ApplyCompType,
        RenameFunctionFailed,
        RenameArgumentFailed,
        NoSuchArgument,
        ReturnCompType
      ),
    RenameError
      ( InvalidAbstractionReference,
        IrrelevantAbstraction,
        UndeterminedAbstraction
      ),
    arg,
    builtin1,
    builtin2,
    builtin3,
    force,
    ret,
    err,
    lit,
    thunk,
  )
where

import Control.Monad.Except (MonadError (throwError))
import Control.Monad.HashCons (MonadHashCons (refTo))
import Control.Monad.Reader (MonadReader, asks)
import Covenant.Constant (AConstant, typeConstant)
import Covenant.DeBruijn (DeBruijn, asInt)
import Covenant.Index (Index, count0, intIndex)
import Covenant.Internal.Rename
  ( RenameError
      ( InvalidAbstractionReference,
        IrrelevantAbstraction,
        UndeterminedAbstraction
      ),
  )
import Covenant.Internal.Term
  ( ASGNode (ACompNode, AValNode, AnError),
    ASGNodeType (CompNodeType, ErrorNodeType, ValNodeType),
    Arg (Arg),
    CompNodeInfo
      ( Builtin1Internal,
        Builtin2Internal,
        Builtin3Internal,
        ForceInternal,
        ReturnInternal
      ),
    CovenantTypeError
      ( ApplyCompType,
        ApplyToError,
        ApplyToValType,
        BrokenIdReference,
        ForceCompType,
        ForceError,
        ForceNonThunk,
        NoSuchArgument,
        RenameArgumentFailed,
        RenameFunctionFailed,
        ReturnCompType,
        ThunkError,
        ThunkValType
      ),
    Id,
    Ref,
    ValNodeInfo (LitInternal, ThunkInternal),
    typeId,
    typeRef,
  )
import Covenant.Internal.Type
  ( AbstractTy,
    CompT (CompT),
    CompTBody (CompTBody),
    ValT (ThunkT),
  )
import Covenant.Prim
  ( OneArgFunc,
    ThreeArgFunc,
    TwoArgFunc,
    typeOneArgFunc,
    typeThreeArgFunc,
    typeTwoArgFunc,
  )
import Data.Coerce (coerce)
import Data.EnumMap (EnumMap)
import Data.EnumMap qualified as EnumMap
import Data.Kind (Type)
import Data.Maybe (fromJust)
import Data.Vector (Vector)
import Data.Vector.NonEmpty qualified as NonEmpty
import Optics.Core
  ( A_Lens,
    LabelOptic (labelOptic),
    ix,
    lens,
    preview,
    review,
    (%),
  )

-- | @since 1.0.0
newtype ASG = ASG (Id, EnumMap Id ASGNode)
  deriving stock
    ( -- | @since 1.0.0
      Eq,
      -- | @since 1.0.0
      Show
    )

-- Note (Koz, 24/04/25): The `rootNode` and `nodeAt` functions use `fromJust`,
-- because we can guarantee it's impossible to miss. For an end user, the only
-- way to get hold of an `Id` is by inspecting a node, and since we control how
-- these are built and assigned, and users can't change them, it's safe.
--
-- It is technically possible to escape this safety regime by having two
-- different `ASG`s and mixing up their `Id`s. However, this is both vanishingly
-- unlikely and probably not worth trying to protect against, given the nuisance
-- of having to work in `Maybe` all the time.

-- | @since 1.0.0
rootNode :: ASG -> ASGNode
rootNode asg@(ASG (rootId, _)) = nodeAt rootId asg

-- | @since 1.0.0
nodeAt :: Id -> ASG -> ASGNode
nodeAt i (ASG (_, mappings)) = fromJust . EnumMap.lookup i $ mappings

-- | @since 1.0.0
newtype ScopeInfo = ScopeInfo (Vector (Vector (ValT AbstractTy)))
  deriving stock
    ( -- | @since 1.0.0
      Eq,
      -- | @since 1.0.0
      Show
    )

-- | @since 1.0.0
instance
  (k ~ A_Lens, a ~ Vector (Vector (ValT AbstractTy)), b ~ Vector (Vector (ValT AbstractTy))) =>
  LabelOptic "argumentInfo" k ScopeInfo ScopeInfo a b
  where
  {-# INLINEABLE labelOptic #-}
  labelOptic = lens coerce (\_ v -> ScopeInfo v)

-- | @since 1.0.0
arg ::
  forall (m :: Type -> Type).
  (MonadError CovenantTypeError m, MonadReader ScopeInfo m) =>
  DeBruijn ->
  Index "arg" ->
  m Arg
arg scope index = do
  let scopeAsInt = asInt scope
  let indexAsInt = review intIndex index
  lookedUp <- asks (preview (#argumentInfo % ix scopeAsInt % ix indexAsInt))
  case lookedUp of
    Nothing -> throwError . NoSuchArgument scope $ index
    Just t -> pure . Arg scope index $ t

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
ret ::
  forall (m :: Type -> Type).
  (MonadHashCons Id ASGNode m, MonadError CovenantTypeError m) =>
  Ref ->
  m Id
ret r = do
  refT <- typeRef r
  case refT of
    ValNodeType t -> do
      let t' = CompT count0 . CompTBody . NonEmpty.singleton $ t
      refTo . ACompNode t' . ReturnInternal $ r
    CompNodeType t -> throwError . ReturnCompType $ t
    ErrorNodeType -> err

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
