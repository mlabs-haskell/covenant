module Covenant.ASG
  ( ScopeInfo,
    Id,
    Ref,
    Arg,
    ASGNode,
    ASG,
    CovenantError (..),
    ASGBuilder,
    runASGBuilder,
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
        ReturnCompType,
        LambdaResultsInValType,
        LambdaResultsInNonReturn,
        ReturnWrapsError,
        ReturnWrapsCompType,
        WrongReturnType,
        UnificationError
      ),
    RenameError
      ( InvalidAbstractionReference,
        IrrelevantAbstraction,
        UndeterminedAbstraction
      ),
    typeASGNode,
    arg,
    builtin1,
    builtin2,
    builtin3,
    force,
    ret,
    lam,
    err,
    lit,
    thunk,
    app,
  )
where

import Control.Monad.Except
  ( ExceptT,
    MonadError (throwError),
    runExceptT,
  )
import Control.Monad.HashCons
  ( HashConsT,
    MonadHashCons (lookupRef, refTo),
    runHashConsT,
  )
import Control.Monad.Reader
  ( MonadReader (local),
    ReaderT,
    asks,
    runReaderT,
  )
import Covenant.Constant (AConstant, typeConstant)
import Covenant.DeBruijn (DeBruijn, asInt)
import Covenant.Index (Index, count0, intIndex)
import Covenant.Internal.Rename
  ( RenameError
      ( InvalidAbstractionReference,
        IrrelevantAbstraction,
        UndeterminedAbstraction
      ),
    renameCompT,
    renameValT,
    runRenameM,
    undoRename,
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
        LamInternal,
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
        LambdaResultsInNonReturn,
        LambdaResultsInValType,
        NoSuchArgument,
        RenameArgumentFailed,
        RenameFunctionFailed,
        ReturnCompType,
        ReturnWrapsCompType,
        ReturnWrapsError,
        ThunkError,
        ThunkValType,
        UnificationError,
        WrongReturnType
      ),
    Id,
    Ref,
    ValNodeInfo (AppInternal, LitInternal, ThunkInternal),
    typeId,
    typeRef,
  )
import Covenant.Internal.Type
  ( AbstractTy,
    CompT (CompT),
    CompTBody (CompTBody),
    Renamed,
    ValT (ThunkT),
  )
import Covenant.Internal.Unification (checkApp)
import Covenant.Prim
  ( OneArgFunc,
    ThreeArgFunc,
    TwoArgFunc,
    typeOneArgFunc,
    typeThreeArgFunc,
    typeTwoArgFunc,
  )
import Data.Bimap (Bimap)
import Data.Bimap qualified as Bimap
import Data.Coerce (coerce)
import Data.Functor.Identity (Identity, runIdentity)
import Data.Kind (Type)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe (fromJust)
import Data.Vector (Vector)
import Data.Vector qualified as Vector
import Data.Vector.NonEmpty qualified as NonEmpty
import Optics.Core
  ( A_Lens,
    LabelOptic (labelOptic),
    ix,
    lens,
    over,
    preview,
    review,
    (%),
  )

-- | @since 1.0.0
newtype ASG = ASG (Id, Map Id ASGNode)
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
nodeAt i (ASG (_, mappings)) = fromJust . Map.lookup i $ mappings

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
data CovenantError
  = TypeError (Bimap Id ASGNode) CovenantTypeError
  | EmptyASG
  | TopLevelError
  | TopLevelValue (Bimap Id ASGNode) (ValT AbstractTy) ValNodeInfo

-- | @since 1.0.0
newtype ASGBuilder (a :: Type)
  = ASGBuilder (ReaderT ScopeInfo (ExceptT CovenantTypeError (HashConsT Id ASGNode Identity)) a)
  deriving
    ( -- | @since 1.0.0
      Functor,
      -- | @since 1.0.0
      Applicative,
      -- | @since 1.0.0
      Monad,
      -- | @since 1.0.0
      MonadReader ScopeInfo,
      -- | @since 1.0.0
      MonadError CovenantTypeError,
      -- | @since 1.0.0
      MonadHashCons Id ASGNode
    )
    via ReaderT ScopeInfo (ExceptT CovenantTypeError (HashConsT Id ASGNode Identity))

-- | @since 1.0.0
runASGBuilder ::
  forall (a :: Type).
  ASGBuilder a ->
  Either CovenantError ASG
runASGBuilder (ASGBuilder comp) =
  case runIdentity . runHashConsT . runExceptT . runReaderT comp . ScopeInfo $ Vector.empty of
    (result, bm) -> case result of
      Left err' -> Left . TypeError bm $ err'
      Right _ -> case Bimap.size bm of
        0 -> Left EmptyASG
        _ -> do
          let (i, rootNode') = Bimap.findMax bm
          case rootNode' of
            AnError -> Left TopLevelError
            ACompNode _ _ -> pure . ASG $ (i, Bimap.toMap bm)
            AValNode t info -> Left . TopLevelValue bm t $ info

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
lam ::
  forall (m :: Type -> Type).
  (MonadHashCons Id ASGNode m, MonadError CovenantTypeError m, MonadReader ScopeInfo m) =>
  CompT AbstractTy ->
  m Id ->
  m Id
lam expectedT@(CompT _ (CompTBody xs)) bodyComp = do
  let (args, resultT) = NonEmpty.unsnoc xs
  bodyId <- local (over #argumentInfo (Vector.cons args)) bodyComp
  bodyNode <- lookupRef bodyId
  case bodyNode of
    Nothing -> throwError . BrokenIdReference $ bodyId
    -- This unifies with anything, so we're fine
    Just AnError -> refTo . ACompNode expectedT . LamInternal $ bodyId
    Just (ACompNode t specs) -> case specs of
      ReturnInternal r -> do
        rT <- typeRef r
        case rT of
          -- Note (Koz, 17/04/2025): I am not 100% sure about this, but I can't
          -- see how anything else would make sense.
          ValNodeType actualT ->
            if resultT == actualT
              then refTo . ACompNode expectedT . LamInternal $ bodyId
              else throwError . WrongReturnType resultT $ actualT
          ErrorNodeType -> throwError ReturnWrapsError
          CompNodeType t' -> throwError . ReturnWrapsCompType $ t'
      _ -> throwError . LambdaResultsInNonReturn $ t
    Just (AValNode t _) -> throwError . LambdaResultsInValType $ t

-- | @since 1.0.0
err ::
  forall (m :: Type -> Type).
  (MonadHashCons Id ASGNode m) =>
  m Id
err = refTo AnError

-- | @since 1.0.0
app ::
  forall (m :: Type -> Type).
  (MonadHashCons Id ASGNode m, MonadError CovenantTypeError m) =>
  Id ->
  Vector Ref ->
  m Id
app fId argRefs = do
  lookedUp <- typeId fId
  case lookedUp of
    CompNodeType fT -> case runRenameM . renameCompT $ fT of
      Left err' -> throwError . RenameFunctionFailed fT $ err'
      Right renamedFT -> do
        renamedArgs <- traverse renameArg argRefs
        case checkApp renamedFT . Vector.toList $ renamedArgs of
          Left err' -> throwError . UnificationError $ err'
          Right result -> do
            let restored = undoRename result
            refTo . AValNode restored . AppInternal fId $ argRefs
    ValNodeType t -> throwError . ApplyToValType $ t
    ErrorNodeType -> throwError ApplyToError

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

-- Helpers

renameArg ::
  forall (m :: Type -> Type).
  (MonadHashCons Id ASGNode m, MonadError CovenantTypeError m) =>
  Ref -> m (Maybe (ValT Renamed))
renameArg r =
  typeRef r >>= \case
    CompNodeType t -> throwError . ApplyCompType $ t
    ValNodeType t -> case runRenameM . renameValT $ t of
      Left err' -> throwError . RenameArgumentFailed t $ err'
      Right renamed -> pure . Just $ renamed
    ErrorNodeType -> pure Nothing
