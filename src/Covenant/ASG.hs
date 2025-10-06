{-# LANGUAGE CPP #-}
{-# LANGUAGE PatternSynonyms #-}

-- |
-- Module: Covenant.ASG
-- Copyright: (C) MLabs 2025
-- License: Apache 2.0
-- Maintainer: koz@mlabs.city, sean@mlabs.city
--
-- The Covenant ASG, and ways to programmatically build it.
--
-- = Note
--
-- We use the term \'ASG\' to refer to \'abstract syntax graph\'. This is
-- because Covenant uses hash consing to ensure duplicate nodes do not exist,
-- thus producing a DAG structure, rather than a tree.
--
-- @since 1.0.0
module Covenant.ASG
  ( -- * The ASG itself

    -- ** Types
    ASG (ASG),

    -- ** Functions
    topLevelId,
    topLevelNode,
    nodeAt,

    -- * ASG components

    -- ** Types
    Id,
    Ref (..),
    Arg,
    CompNodeInfo
      ( Builtin1,
        Builtin2,
        Builtin3,
        Builtin6,
        Lam,
        Force
      ),
    ValNodeInfo (Lit, App, Thunk, Cata, DataConstructor, Match),
    ASGNode (..),
    ASGNodeType (..),

    -- ** Functions
    typeASGNode,

    -- * ASG builder

    -- ** Types
    CovenantError (..),
    ScopeInfo (..),
    ASGBuilder,
    TypeAppError (..),
    RenameError (..),
    UnRenameError (..),
    EncodingArgErr (..),
    CovenantTypeError (..),
    BoundTyVar,

    -- ** Introducers
    boundTyVar,
    arg,
    builtin1,
    builtin2,
    builtin3,
    builtin6,
    force,
    lam,
    err,
    lit,
    thunk,
    dataConstructor,

    -- ** Eliminators
    app,
    cata,
    match,

    -- ** Helpers
    ctor,
    ctor',
    lazyLam,
    dtype,
    baseFunctorOf,
    naturalBF,
    negativeBF,
    app',

    -- *** Environment
    defaultDatatypes,

    -- *** Function
    runASGBuilder,
    -- only for tests
    ASGEnv (..),
  )
where

#if __GLASGOW_HASKELL__==908
import Data.Foldable (foldl')
#endif

import Control.Monad (foldM, join, unless, zipWithM)
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
import Covenant.Data (DatatypeInfo, mkDatatypeInfo, primBaseFunctorInfos)
import Covenant.DeBruijn (DeBruijn (S, Z), asInt)
import Covenant.Index (Count, Index, count0, intCount, intIndex, wordCount)
import Covenant.Internal.KindCheck (EncodingArgErr (EncodingArgMismatch), checkEncodingArgs)
import Covenant.Internal.Ledger (ledgerTypes)
import Covenant.Internal.Rename
  ( RenameError
      ( InvalidAbstractionReference,
        InvalidScopeReference
      ),
    UnRenameError (NegativeDeBruijn, UnRenameWildCard),
    renameCompT,
    renameDatatypeInfo,
    renameValT,
    runRenameM,
    undoRename,
  )
import Covenant.Internal.Term
  ( ASGNode (ACompNode, AValNode, AnError),
    ASGNodeType (CompNodeType, ErrorNodeType, ValNodeType),
    Arg (Arg),
    BoundTyVar (BoundTyVar),
    CompNodeInfo
      ( Builtin1Internal,
        Builtin2Internal,
        Builtin3Internal,
        Builtin6Internal,
        ForceInternal,
        LamInternal
      ),
    CovenantTypeError
      ( ApplyCompType,
        ApplyToError,
        ApplyToValType,
        BaseFunctorDoesNotExistFor,
        BrokenIdReference,
        CataAlgebraWrongArity,
        CataApplyToNonValT,
        CataNoBaseFunctorForType,
        CataNoSuchType,
        CataNonRigidAlgebra,
        CataNotAnAlgebra,
        CataUnsuitable,
        CataWrongBuiltinType,
        CataWrongValT,
        ConstructorDoesNotExistForType,
        DatatypeInfoRenameError,
        EncodingError,
        FailedToRenameInstantiation,
        ForceCompType,
        ForceError,
        ForceNonThunk,
        IntroFormErrorNodeField,
        IntroFormWrongNumArgs,
        InvalidOpaqueField,
        LambdaResultsInCompType,
        LambdaResultsInNonReturn,
        MatchErrorAsHandler,
        MatchNoBBForm,
        MatchNoDatatypeInfo,
        MatchNonDatatypeScrutinee,
        MatchNonThunkBBF,
        MatchNonValTy,
        MatchPolymorphicHandler,
        MatchRenameBBFail,
        MatchRenameTyConArgFail,
        NoSuchArgument,
        OutOfScopeTyVar,
        RenameArgumentFailed,
        RenameFunctionFailed,
        ReturnCompType,
        ReturnWrapsCompType,
        ReturnWrapsError,
        ThunkError,
        ThunkValType,
        TypeDoesNotExist,
        UndeclaredOpaquePlutusDataCtor,
        UndoRenameFailure,
        UnificationError,
        WrongNumInstantiationsInApp,
        WrongReturnType
      ),
    Id,
    Ref (AnArg, AnId),
    ValNodeInfo (AppInternal, CataInternal, DataConstructorInternal, LitInternal, MatchInternal, ThunkInternal),
    typeASGNode,
    typeId,
    typeRef,
  )
import Covenant.Internal.Type
  ( AbstractTy (BoundAt),
    BuiltinFlatT (ByteStringT, IntegerT),
    CompT (CompT),
    CompTBody (CompTBody),
    DataDeclaration (DataDeclaration),
    Renamed,
    TyName,
    ValT (BuiltinFlat, Datatype, ThunkT),
    arity,
  )
import Covenant.Internal.Unification
  ( TypeAppError
      ( DatatypeInfoRenameFailed,
        DoesNotUnify,
        ExcessArgs,
        ImpossibleHappened,
        InsufficientArgs,
        LeakingUnifiable,
        LeakingWildcard,
        NoBBForm,
        NoDatatypeInfo
      ),
    UnifyM,
    checkApp,
    fixUp,
    reconcile,
    runUnifyM,
    substitute,
    unify,
  )
import Covenant.Prim
  ( OneArgFunc,
    SixArgFunc,
    ThreeArgFunc,
    TwoArgFunc,
    typeOneArgFunc,
    typeSixArgFunc,
    typeThreeArgFunc,
    typeTwoArgFunc,
  )
import Covenant.Type
  ( CompT (Comp0),
    CompTBody (ReturnT),
    Constructor,
    ConstructorName,
    DataDeclaration (OpaqueData),
    PlutusDataConstructor (PlutusB, PlutusConstr, PlutusI, PlutusList, PlutusMap),
    Renamed (Unifiable),
    TyName (TyName),
    ValT (Abstraction),
    tyvar,
  )
import Data.Bimap (Bimap)
import Data.Bimap qualified as Bimap
import Data.Coerce (coerce)
import Data.Functor.Identity (Identity, runIdentity)
import Data.Kind (Type)
import Data.List (find)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe (fromJust, isJust, mapMaybe)
import Data.Set qualified as Set
import Data.Text qualified as T
import Data.Vector (Vector)
import Data.Vector qualified as Vector
import Data.Vector.NonEmpty qualified as NonEmpty
import Data.Void (Void, vacuous)
import Data.Wedge (Wedge (Nowhere), wedge)
import Data.Word (Word32)
import Optics.Core
  ( A_Lens,
    LabelOptic (labelOptic),
    at,
    folded,
    ix,
    lens,
    over,
    preview,
    review,
    toListOf,
    view,
    (%),
    _1,
    _2,
  )

-- | A fully-assembled Covenant ASG.
--
-- @since 1.0.0
newtype ASG = ASGInternal (Id, Map Id ASGNode)
  deriving stock
    ( -- | @since 1.0.0
      Eq,
      -- | @since 1.0.0
      Show
    )

{-# COMPLETE ASG #-}

pattern ASG :: Map Id ASGNode -> ASG
pattern ASG m <- ASGInternal (_, m)

-- Note (Koz, 24/04/25): The `topLevelNode` and `nodeAt` functions use `fromJust`,
-- because we can guarantee it's impossible to miss. For an end user, the only
-- way to get hold of an `Id` is by inspecting a node, and since we control how
-- these are built and assigned, and users can't change them, it's safe.
--
-- It is technically possible to escape this safety regime by having two
-- different `ASG`s and mixing up their `Id`s. However, this is both vanishingly
-- unlikely and probably not worth trying to protect against, given the nuisance
-- of having to work in `Maybe` all the time.

-- | Retrieves the top-level 'Id' of an ASG.
--
-- @since 1.3.0
topLevelId :: ASG -> Id
topLevelId (ASGInternal (i, _)) = i

-- | Retrieves the top-level node of an ASG.
--
-- @since 1.0.0
topLevelNode :: ASG -> ASGNode
topLevelNode asg@(ASGInternal (rootId, _)) = nodeAt rootId asg

-- | Given an 'Id' and an ASG, produces the node corresponding to that 'Id'.
--
-- = Important note
--
-- This is only safe to use if the 'Id' comes from a node in the argument 'ASG'.
-- 'Id's valid in one ASG are not likely to be valid in another. \'Mixing
-- and matching\' 'Id's from different ASGs will at best produce unexpected
-- results, and at worst will crash. You have been warned.
--
-- @since 1.0.0
nodeAt :: Id -> ASG -> ASGNode
nodeAt i (ASG mappings) = fromJust . Map.lookup i $ mappings

-- | The environment used when \'building up\' an 'ASG'. This type is exposed
-- only for testing, or debugging, and should /not/ be used in general by those
-- who just want to build an 'ASG'.
--
-- @since 1.2.0
data ASGEnv = ASGEnv ScopeInfo (Map TyName (DatatypeInfo AbstractTy))

-- | @since 1.2.0
instance
  (k ~ A_Lens, a ~ ScopeInfo, b ~ ScopeInfo) =>
  LabelOptic "scopeInfo" k ASGEnv ASGEnv a b
  where
  {-# INLINEABLE labelOptic #-}
  labelOptic =
    lens
      (\(ASGEnv si _) -> si)
      (\(ASGEnv _ dti) si -> ASGEnv si dti)

-- | @since 1.2.0
instance
  (k ~ A_Lens, a ~ Map TyName (DatatypeInfo AbstractTy), b ~ Map TyName (DatatypeInfo AbstractTy)) =>
  LabelOptic "datatypeInfo" k ASGEnv ASGEnv a b
  where
  {-# INLINEABLE labelOptic #-}
  labelOptic =
    lens
      (\(ASGEnv _ dti) -> dti)
      (\(ASGEnv si _) dti -> ASGEnv si dti)

-- | A tracker for scope-related information while building an ASG
-- programmatically. Currently only tracks available arguments.
--
-- = Important note
--
-- This is a fairly low-level type, designed specifically for ASG construction.
-- While you can do arbitrary things with it, changing things in it outside of
-- the functionality provided by this module is not recommended, unless you know
-- /exactly/ what you're doing.
--
-- @since 1.2.0
newtype ScopeInfo = ScopeInfo (Vector (Word32, Vector (ValT AbstractTy)))
  deriving stock
    ( -- | @since 1.0.0
      Eq,
      -- | @since 1.0.0
      Show
    )

-- | Gives access to the argument information for the current, and all
-- enclosing, scopes. The \'outer\' 'Vector' is a stack of scopes, with lower
-- indexes corresponding to closer scopes: index 0 is our scope, 1 is our
-- enclosing scope, 2 is the enclosing scope of our enclosing scope, etc. The
-- \'inner\' 'Vector's are positional lists of argument types.
--
-- @since 1.2.0
instance
  (k ~ A_Lens, a ~ Vector (Word32, Vector (ValT AbstractTy)), b ~ Vector (Word32, Vector (ValT AbstractTy))) =>
  LabelOptic "argumentInfo" k ScopeInfo ScopeInfo a b
  where
  {-# INLINEABLE labelOptic #-}
  labelOptic = lens coerce (\_ v -> ScopeInfo v)

-- | A Plutus primop with one argument.
--
-- @since 1.0.0
pattern Builtin1 :: OneArgFunc -> CompNodeInfo
pattern Builtin1 f <- Builtin1Internal f

-- | A Plutus primop with two arguments.
--
-- @since 1.0.0
pattern Builtin2 :: TwoArgFunc -> CompNodeInfo
pattern Builtin2 f <- Builtin2Internal f

-- | A Plutus primop with three arguments.
--
-- @since 1.0.0
pattern Builtin3 :: ThreeArgFunc -> CompNodeInfo
pattern Builtin3 f <- Builtin3Internal f

-- | A Plutus primop with six arguments.
--
-- @since 1.1.0
pattern Builtin6 :: SixArgFunc -> CompNodeInfo
pattern Builtin6 f <- Builtin6Internal f

-- | Force a thunk back into the computation it wraps.
--
-- @since 1.0.0
pattern Force :: Ref -> CompNodeInfo
pattern Force r <- ForceInternal r

-- | A lambda.
--
-- @since 1.2.0
pattern Lam :: Ref -> CompNodeInfo
pattern Lam r <- LamInternal r

{-# COMPLETE Builtin1, Builtin2, Builtin3, Builtin6, Force, Lam #-}

-- | A compile-time literal of a flat builtin type.
--
-- @since 1.0.0
pattern Lit :: AConstant -> ValNodeInfo
pattern Lit c <- LitInternal c

-- | An application of a computation (the 'Id' field) to some arguments (the
-- 'Vector' field).
--
-- @since 1.0.0
pattern App :: Id -> Vector Ref -> Vector (Wedge BoundTyVar (ValT Void)) -> ValNodeInfo
pattern App f args instTys <- AppInternal f args instTys

-- | Wrap a computation into a value (essentially delaying it).
--
-- @since 1.0.0
pattern Thunk :: Id -> ValNodeInfo
pattern Thunk i <- ThunkInternal i

-- | \'Tear down\' a self-recursive value with an algebra.
--
-- @since 1.0.0
pattern Cata :: Ref -> Ref -> ValNodeInfo
pattern Cata algebraRef valRef <- CataInternal algebraRef valRef

-- | Inject (zero or more) fields into a data constructor
--
-- @since 1.2.0
pattern DataConstructor :: TyName -> ConstructorName -> Vector Ref -> ValNodeInfo
pattern DataConstructor tyName ctorName fields <- DataConstructorInternal tyName ctorName fields

-- | Deconstruct a value of a data type using the supplied handlers for each arm
--
-- @since 1.2.0
pattern Match :: Ref -> Vector Ref -> ValNodeInfo
pattern Match scrutinee handlers <- MatchInternal scrutinee handlers

{-# COMPLETE Lit, App, Thunk, Cata, DataConstructor, Match #-}

-- | Any problem that might arise when building an ASG programmatically.
--
-- @since 1.0.0
data CovenantError
  = -- | There was a type error when assembling the ASG. This provides the
    -- hash-consed state up to the point of the error.
    --
    -- @since 1.0.0
    TypeError (Bimap Id ASGNode) CovenantTypeError
  | -- | We tried to generate an ASG with no nodes in it.
    --
    -- @since 1.0.0
    EmptyASG
  | -- | We tried to generate as ASG whose top-level node is an error.
    --
    -- @since 1.0.0
    TopLevelError
  | -- | We tried to generate an ASG whose top-level node is a value.
    --
    -- @since 1.0.0
    TopLevelValue (Bimap Id ASGNode) (ValT AbstractTy) ValNodeInfo
  deriving stock
    ( -- | @since 1.0.0
      Eq,
      -- | @since 1.0.0
      Show
    )

-- | A concrete monadic stack, providing the minimum amount of functionality
-- needed to build an ASG using the combinators given in this module.
--
-- @since 1.0.0
newtype ASGBuilder (a :: Type)
  = ASGBuilder (ReaderT ASGEnv (ExceptT CovenantTypeError (HashConsT Id ASGNode Identity)) a)
  deriving
    ( -- | @since 1.0.0
      Functor,
      -- | @since 1.0.0
      Applicative,
      -- | @since 1.0.0
      Monad,
      -- | @since 1.1.0
      MonadReader ASGEnv,
      -- | @since 1.0.0
      MonadError CovenantTypeError,
      -- | @since 1.0.0
      MonadHashCons Id ASGNode
    )
    via ReaderT ASGEnv (ExceptT CovenantTypeError (HashConsT Id ASGNode Identity))

-- | A standard collection of types required for almost any realistic script.
-- This includes non-\'flat\' builtin types (such as lists and pairs), as well
-- as all types required by the ledger (including types like @Maybe@).
--
-- @since 1.1.0
defaultDatatypes :: Map TyName (DatatypeInfo AbstractTy)
defaultDatatypes = foldMap go ledgerTypes <> primBaseFunctorInfos
  where
    go :: DataDeclaration AbstractTy -> Map TyName (DatatypeInfo AbstractTy)
    go decl = case mkDatatypeInfo decl of
      Left err' -> error $ "Unexpected failure in default datatypes: " <> show err'
      Right info -> info

-- | Executes an 'ASGBuilder' to make a \'finished\' ASG.
--
-- @since 1.0.0
runASGBuilder ::
  forall (a :: Type).
  Map TyName (DatatypeInfo AbstractTy) ->
  ASGBuilder a ->
  Either CovenantError ASG
runASGBuilder tyDict (ASGBuilder comp) =
  case runIdentity . runHashConsT . runExceptT . runReaderT comp $ ASGEnv (ScopeInfo Vector.empty) tyDict of
    (result, bm) -> case result of
      Left err' -> Left . TypeError bm $ err'
      Right _ -> case Bimap.size bm of
        0 -> Left EmptyASG
        _ -> do
          let (i, rootNode') = Bimap.findMax bm
          case rootNode' of
            AnError -> Left TopLevelError
            ACompNode _ _ -> pure . ASGInternal $ (i, Bimap.toMap bm)
            AValNode t info -> Left . TopLevelValue bm t $ info

-- | Given a scope and a positional argument index, construct that argument.
-- Will fail if that argument doesn't exist in the specified scope, or if the
-- specified scope doesn't exist.
--
-- @since 1.0.0
arg ::
  forall (m :: Type -> Type).
  (MonadError CovenantTypeError m, MonadReader ASGEnv m) =>
  DeBruijn ->
  Index "arg" ->
  m Arg
arg scope index = do
  let scopeAsInt = review asInt scope
  let indexAsInt = review intIndex index
  lookedUp <- asks (preview (#scopeInfo % #argumentInfo % ix scopeAsInt % _2 % ix indexAsInt))
  case lookedUp of
    Nothing -> throwError . NoSuchArgument scope $ index
    Just t -> pure . Arg scope index $ t

-- | Construct a node corresponding to the given Plutus primop.
--
-- @since 1.0.0
builtin1 ::
  forall (m :: Type -> Type).
  (MonadHashCons Id ASGNode m) =>
  OneArgFunc ->
  m Id
builtin1 bi = do
  let node = ACompNode (typeOneArgFunc bi) . Builtin1Internal $ bi
  refTo node

-- | As 'builtin1', but for two-argument primops.
--
-- @since 1.0.0
builtin2 ::
  forall (m :: Type -> Type).
  (MonadHashCons Id ASGNode m) =>
  TwoArgFunc ->
  m Id
builtin2 bi = do
  let node = ACompNode (typeTwoArgFunc bi) . Builtin2Internal $ bi
  refTo node

-- | As 'builtin1', but for three-argument primops.
--
-- @since 1.0.0
builtin3 ::
  forall (m :: Type -> Type).
  (MonadHashCons Id ASGNode m) =>
  ThreeArgFunc ->
  m Id
builtin3 bi = do
  let node = ACompNode (typeThreeArgFunc bi) . Builtin3Internal $ bi
  refTo node

-- | As 'builtin1', but for six-argument primops.
--
-- @since 1.1.0
builtin6 ::
  forall (m :: Type -> Type).
  (MonadHashCons Id ASGNode m) =>
  SixArgFunc ->
  m Id
builtin6 bi = do
  let node = ACompNode (typeSixArgFunc bi) . Builtin6Internal $ bi
  refTo node

-- | Given a reference to a thunk, turn it back into a computation. Will fail if
-- the reference isn't a thunk.
--
-- @since 1.0.0
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

-- | Given a desired type, and a computation which will construct a lambda body
-- when executed (with the scope extended with the arguments the functions can
-- expect), construct a lambda.
--
-- = Important note
--
-- This combinator works slightly differently to the others in this module. This
-- is required because, due to hash consing, an ASG is typically built
-- \'bottom-up\', whereas function arguments (and their scopes) are necessarily
-- top-down. Thus, we need to \'delay\' the construction of a lambda's body to
-- ensure that proper scoped argument information can be given to it, hence why
-- the argument being passed is an @m Ref@.
--
-- @since 1.2.0
lam ::
  forall (m :: Type -> Type).
  (MonadHashCons Id ASGNode m, MonadError CovenantTypeError m, MonadReader ASGEnv m) =>
  CompT AbstractTy ->
  m Ref ->
  m Id
lam expectedT@(CompT cnt (CompTBody xs)) bodyComp = do
  let (args, resultT) = NonEmpty.unsnoc xs
      cntW = view wordCount cnt
  bodyRef <- local (over (#scopeInfo % #argumentInfo) (Vector.cons (cntW, args))) bodyComp
  case bodyRef of
    AnArg (Arg _ _ argTy) -> do
      if argTy == resultT
        then refTo . ACompNode expectedT . LamInternal $ bodyRef
        else throwError . WrongReturnType resultT $ argTy
    AnId bodyId ->
      lookupRef bodyId >>= \case
        Nothing -> throwError . BrokenIdReference $ bodyId
        -- This unifies with anything, so we're fine
        Just AnError -> refTo . ACompNode expectedT . LamInternal . AnId $ bodyId
        Just (AValNode ty _) -> do
          if ty == resultT
            then refTo . ACompNode expectedT . LamInternal . AnId $ bodyId
            else throwError . WrongReturnType resultT $ ty
        Just (ACompNode t _) -> throwError $ LambdaResultsInCompType t

-- | Construct the error node.
--
-- @since 1.0.0
err ::
  forall (m :: Type -> Type).
  (MonadHashCons Id ASGNode m) =>
  m Id
err = refTo AnError

-- | Performs both term and type application. More precisely, given:
--
-- * An 'Id' referring to a computation; and
-- * A 'Vector' of 'Ref's for the desired term arguments to the computation, in
--   order; and
-- * A 'Vector' of (optional) type arguments to the computation, also in order.
--
-- we produce the result of that application.
--
-- This can fail for a range of reasons:
--
-- * Type mismatch between what the computation expects and what it's given
-- * Too many or too few arguments
-- * Not a computation type for 'Id' argument
-- * Not value types for 'Ref's
-- * Renaming failures (likely due to a malformed function or argument type)
--
-- = Note
--
-- We use the 'Wedge' data type to designate type arguments, as it can represent
-- the three possibilities we need:
--
-- * \'Infer this argument\', specified as 'Nowhere'.
-- * \'Use this type variable in our scope\', specified as 'Here'.
-- * \'Use this concrete type\', specified as 'There'.
--
-- @since 1.2.0
app ::
  forall (m :: Type -> Type).
  (MonadHashCons Id ASGNode m, MonadError CovenantTypeError m, MonadReader ASGEnv m) =>
  Id ->
  Vector Ref ->
  Vector (Wedge BoundTyVar (ValT Void)) ->
  m Id
app fId argRefs instTys = do
  lookedUp <- typeId fId
  let rawSubs = mkSubstitutions instTys
  subs <- renameSubs rawSubs
  scopeInfo <- askScope
  case lookedUp of
    CompNodeType fT -> case runRenameM scopeInfo . renameCompT $ fT of
      Left err' -> throwError . RenameFunctionFailed fT $ err'
      Right renamedFT@(CompT count _) -> do
        let numInstantiations = Vector.length instTys
            numVars = review intCount count
        if numInstantiations /= numVars
          then throwError $ WrongNumInstantiationsInApp renamedFT numVars numInstantiations
          else do
            instantiatedFT <- instantiate subs renamedFT
            renamedArgs <- traverse renameArg argRefs
            tyDict <- asks (view #datatypeInfo)
            result <- either (throwError . UnificationError) pure $ checkApp tyDict instantiatedFT (Vector.toList renamedArgs)
            restored <- undoRenameM result
            checkEncodingWithInfo tyDict restored
            refTo . AValNode restored $ AppInternal fId argRefs instTys
    ValNodeType t -> throwError . ApplyToValType $ t
    ErrorNodeType -> throwError ApplyToError
  where
    mkSubstitutions :: Vector (Wedge BoundTyVar (ValT Void)) -> [(Index "tyvar", ValT AbstractTy)]
    mkSubstitutions =
      Vector.ifoldl'
        ( \acc i' w ->
            let i = fromJust . preview intIndex $ i'
             in wedge
                  acc
                  (\(BoundTyVar dbIx posIx) -> (i, tyvar dbIx posIx) : acc)
                  (\v -> (i, vacuous v) : acc)
                  w
        )
        []

    renameSubs :: [(Index "tyvar", ValT AbstractTy)] -> m [(Index "tyvar", ValT Renamed)]
    renameSubs subs =
      askScope >>= \scope -> case traverse (traverse (runRenameM scope . renameValT)) subs of
        Left err' -> throwError $ FailedToRenameInstantiation err'
        Right res -> pure res

    instantiate :: [(Index "tyvar", ValT Renamed)] -> CompT Renamed -> m (CompT Renamed)
    instantiate [] fn = pure fn
    instantiate subs fn = do
      instantiated <- liftUnifyM . fixUp $ foldr (\(i, t) f -> substitute i t f) (ThunkT fn) subs
      case instantiated of
        ThunkT res -> pure res
        other ->
          throwError . UnificationError . ImpossibleHappened $
            "Impossible happened: Result of tyvar instantiation should be a thunk, but is: "
              <> T.pack (show other)

-- | Introduce a data constructor.
--
-- The first argument is a type name (for example, @\"Maybe\"@). The second
-- argument is a constructor of that type (for example, @\"Just\"@ or
-- @\"Nothing\"@). The third argument are the values to \'fill in\' all the fields
-- of the constructor requested.
--
-- = Note
--
-- 'dataConstructor' yields thunks, which must be forced, and then possibly have
-- type arguments applied to them. The reason for this is subtle, but important.
-- Consider the @Nothing@ constructor of @Maybe@: as this has no fields, we
-- cannot use the field type to determine what the type argument to @Maybe@
-- should be in this case. As datatype terms are values, they do not bind type
-- variables, and thus, we cannot have a return type that makes sense in this
-- case.
--
-- We resolve this problem by returning a thunk. In the case of our example,
-- @Nothing@ would produce @<forall a . !Maybe a>@.
--
-- @since 1.2.0
dataConstructor ::
  forall (m :: Type -> Type).
  (MonadHashCons Id ASGNode m, MonadError CovenantTypeError m, MonadReader ASGEnv m) =>
  TyName ->
  ConstructorName ->
  Vector Ref ->
  m Id
dataConstructor tyName ctorName fields = do
  thisTyInfo <- lookupDatatypeInfo
  let thisTyDecl = view #originalDecl thisTyInfo
  renamedFieldTypes <-
    traverse renameArg fields
      >>= ( \case
              Nothing -> throwError $ IntroFormErrorNodeField tyName ctorName fields
              Just ok -> pure ok
          )
        . sequence
  {- The procedures for handling a typed declared as Opaque and a "normal" type are totally different.

     For Opaque types, we just have to check that the "ConstructorName" we get corresponds to a constructor of
     PlutusData, then validate that the arguments conform with that PlutusData constructor.
  -}
  case thisTyDecl of
    OpaqueData _ opaqueCtorSet -> do
      checkOpaqueArgs opaqueCtorSet renamedFieldTypes
      refTo $ AValNode (Datatype tyName mempty) (DataConstructorInternal tyName ctorName fields)
    DataDeclaration _ count ctors _ -> do
      -- First we check that the arity of the constructor is equal to the number of fields in the decl.
      checkFieldArity (Vector.length fields) thisTyInfo
      -- Then we resolve the supplied field Refs, rename, and throw an error if we're passed an error node.

      -- Then we construct the return type.
      resultThunk <- mkResultThunk count ctors renamedFieldTypes
      -- Then we undo the renaming.
      restored <- undoRenameM resultThunk
      -- Then we check the compatibility of the arguments with the datatype's encoding.
      asks (view #datatypeInfo) >>= \dti -> checkEncodingWithInfo dti restored
      -- Finally, if nothing has thrown an error, we return a reference to our result node, decorated with the
      -- return type we constructed.
      refTo $ AValNode restored (DataConstructorInternal tyName ctorName fields)
  where
    {- Constructs the result type of the introduction form. Arguments are:
         1. The count (number of tyvars) from the data declaration.
         2. The vector of constructors from the data declaration.
         3. The (renamed and resolved) vector of supplied arguments.

       The procedure goes like:
         1. Extract the argument types from the constructor in the declaration. Any tyvars here
            *have* to be Unifiable (unless something has slipped past the kind checker) -
            data declarations have atomic, independent scopes.
         2. Unify those with the actual, supplied field types, yielding a set of substitutions.
         3. Construct a fully abstract (i.e. parameterized only by unifiable type variables) representation of the
            type constructor.
         4. Apply those substitutions to the abstract type constructor.
         5. Wrap the "concretified" type constructor in a thunk and use `fixUp` to sort out the `Count` and
            indices.
    -}
    mkResultThunk :: Count "tyvar" -> Vector (Constructor Renamed) -> Vector (ValT Renamed) -> m (ValT Renamed)
    mkResultThunk count' declCtors fieldArgs' = do
      declCtorFields <- Vector.toList . view #constructorArgs <$> findConstructor declCtors
      subs <- unifyFields declCtorFields fieldArgs
      let tyConAbstractArgs = mapMaybe (fmap (Abstraction . Unifiable) . preview intIndex) [0, 1 .. (count - 1)]
          tyConAbstract = Datatype tyName (Vector.fromList tyConAbstractArgs)
      let tyConConcrete = Map.foldlWithKey' (\acc i t -> substitute i t acc) tyConAbstract subs
      liftUnifyM . fixUp . ThunkT . Comp0 . ReturnT $ tyConConcrete
      where
        count :: Int
        count = review intCount count'

        fieldArgs :: [ValT Renamed]
        fieldArgs = Vector.toList fieldArgs'

    {- Unifies the declaration fields (which may be abstract) with the supplied fields
       (which will be "concrete", in the sense that "they have to be rigid if they're tyvars").

       Returns a (reconciled) set of substitutions which can be applied to a fully-abstract (i.e.
       parameterized only by Unifiable tyVars) to yield the concrete, applied type constructor.
    -}
    unifyFields :: [ValT Renamed] -> [ValT Renamed] -> m (Map (Index "tyvar") (ValT Renamed))
    unifyFields declFields suppliedFields = liftUnifyM $ do
      rawSubs <- zipWithM unify declFields suppliedFields
      foldM reconcile Map.empty rawSubs

    {- Checks that the number of fields supplied as arguments is equal to the
       number of fields in the corresponding constructor of the data declaration.

       This is needed because `zipWithM unifyFields` won't throw an error in the case that they are not equal.
    -}
    checkFieldArity :: Int -> DatatypeInfo Renamed -> m ()
    checkFieldArity actualNumFields dtInfo = do
      let ctors = toListOf (#originalDecl % #datatypeConstructors % folded) dtInfo
      expectedNumFields <- Vector.length . view #constructorArgs <$> findConstructor ctors
      unless (actualNumFields == expectedNumFields) $
        throwError $
          IntroFormWrongNumArgs tyName ctorName actualNumFields

    checkOpaqueArgs :: Set.Set PlutusDataConstructor -> Vector (ValT Renamed) -> m ()
    checkOpaqueArgs declCtors fieldArgs' = case ctorName of
      "I" -> opaqueCheck PlutusI [BuiltinFlat IntegerT]
      "B" -> opaqueCheck PlutusB [BuiltinFlat ByteStringT]
      "List" -> opaqueCheck PlutusList [Datatype "List" (Vector.fromList [Datatype "Data" mempty])]
      "Map" -> opaqueCheck PlutusMap [Datatype "Map" (Vector.fromList [Datatype "Data" mempty, Datatype "Data" mempty])]
      "Constr" -> opaqueCheck PlutusConstr [BuiltinFlat IntegerT, Datatype "List" (Vector.fromList [Datatype "Data" mempty])]
      _ -> throwError $ UndeclaredOpaquePlutusDataCtor declCtors ctorName
      where
        fieldArgs :: [ValT Renamed]
        fieldArgs = Vector.toList fieldArgs'
        opaqueCheck :: PlutusDataConstructor -> [ValT Renamed] -> m ()
        opaqueCheck setMustHaveThis fieldShouldBeThis = do
          unless (setMustHaveThis `Set.member` declCtors) $ throwError (UndeclaredOpaquePlutusDataCtor declCtors ctorName)
          unless (fieldArgs == fieldShouldBeThis) $ throwError (InvalidOpaqueField declCtors ctorName fieldArgs)

    -- convenience helpers

    -- Looks up a constructor in a foldable container of constructors (which is probably always a vector but w/e)
    -- Exists to avoid duplicating this code in a few places.
    findConstructor ::
      forall (t :: Type -> Type) (a :: Type).
      (Foldable t) =>
      t (Constructor a) ->
      m (Constructor a)
    findConstructor xs = case find (\x -> view #constructorName x == ctorName) xs of
      Nothing -> throwError $ ConstructorDoesNotExistForType tyName ctorName
      Just ctor'' -> pure ctor''

    -- Looks up the DatatypeInfo for the type argument supplied
    -- and also renames (and rethrows the rename error if renaming fails)
    lookupDatatypeInfo :: m (DatatypeInfo Renamed)
    lookupDatatypeInfo =
      asks (preview (#datatypeInfo % ix tyName)) >>= \case
        Nothing -> throwError $ TypeDoesNotExist tyName
        Just infoAbstract -> case renameDatatypeInfo infoAbstract of
          Left e -> throwError $ DatatypeInfoRenameError e
          Right infoRenamed -> pure infoRenamed

-- | Construct a node corresponding to the given constant.
--
-- @since 1.0.0
lit ::
  forall (m :: Type -> Type).
  (MonadHashCons Id ASGNode m) =>
  AConstant ->
  m Id
lit c = refTo . AValNode (typeConstant c) . LitInternal $ c

-- | Given an 'Id' referring to a computation, build a thunk wrapping it. Will
-- fail if the 'Id' does not refer to a computation node.
--
-- @since 1.0.0
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

-- | Given a 'Ref' to an algebra (that is, something taking a base functor and
-- producing some result), and a 'Ref' to a value associated with that base
-- functor, build a catamorphism to tear it down. This can fail for a range of
-- reasons:
--
-- * First 'Ref' is not a thunk taking one argument
-- * The argument to the thunk isn't a base functor, or isn't a suitable base
--   functor for the second argument
-- * Second argument is not a value type
--
-- = Note
--
-- 'cata' cannot work with /non-rigid/ algebras; that is, all algebras must be
-- functions that bind no type variables of their own.
--
-- @since 1.1.0
cata ::
  forall (m :: Type -> Type).
  (MonadHashCons Id ASGNode m, MonadError CovenantTypeError m, MonadReader ASGEnv m) =>
  Ref ->
  Ref ->
  m Id
cata rAlg rVal =
  typeRef rVal >>= \case
    ValNodeType valT ->
      typeRef rAlg >>= \case
        t@(ValNodeType (ThunkT algT)) -> case algT of
          Comp0 (CompTBody nev) -> do
            let algebraArity = arity algT
            unless (algebraArity == 1) (throwError . CataAlgebraWrongArity $ algebraArity)
            case nev NonEmpty.! 0 of
              Datatype bfName bfTyArgs -> do
                -- If we got this far, we know at minimum that we have somewhat
                -- sensical arguments. Now we have to make sure that we have a
                -- suitable type for the algebra, and a suitable thing to tear
                -- down.
                --
                -- After verifying this, we use `tryApply` so the unification
                -- machinery can produce the type we expect with proper
                -- concretifications.
                unless (Vector.length bfTyArgs > 0) (throwError . CataNotAnAlgebra $ t)
                let lastTyArg = Vector.last bfTyArgs
                unless (nev NonEmpty.! 1 == lastTyArg) (throwError . CataNotAnAlgebra $ t)
                appliedArgT <- case valT of
                  BuiltinFlat bT -> case bT of
                    ByteStringT -> do
                      unless (bfName == "#ByteString") (throwError . CataUnsuitable algT $ valT)
                      pure $ Datatype "#ByteString" . Vector.singleton $ lastTyArg
                    IntegerT -> do
                      let isSuitableBaseFunctor = bfName == "#Natural" || bfName == "#Negative"
                      unless isSuitableBaseFunctor (throwError . CataUnsuitable algT $ valT)
                      pure $ Datatype bfName . Vector.singleton $ lastTyArg
                    _ -> throwError . CataWrongBuiltinType $ bT
                  Datatype tyName tyVars -> do
                    lookedUp <- asks (view (#datatypeInfo % at tyName))
                    case lookedUp of
                      Nothing -> throwError . CataNoSuchType $ tyName
                      Just info -> case view #baseFunctor info of
                        Just (DataDeclaration actualBfName _ _ _, _) -> do
                          unless (bfName == actualBfName) (throwError . CataUnsuitable algT $ valT)
                          let lastTyArg' = stepDownDB lastTyArg
                          pure . Datatype bfName . Vector.snoc tyVars $ lastTyArg'
                        _ -> throwError . CataNoBaseFunctorForType $ tyName
                  _ -> throwError . CataWrongValT $ valT
                resultT <- tryApply algT appliedArgT
                refTo . AValNode resultT . CataInternal rAlg $ rVal
              _ -> throwError . CataNotAnAlgebra $ t
          _ -> throwError . CataNonRigidAlgebra $ algT
        t -> throwError . CataNotAnAlgebra $ t
    t -> throwError . CataApplyToNonValT $ t

-- | Perform a pattern match. The first argument is the value to be matched on,
-- and the second argument is a 'Vector' of \'handlers\' for each possible
-- \'arm\' of the type of the value to be matched on.
--
-- All handlers must be thunks, and must all return the same (concrete) result.
-- Polymorphic \'handlers\' (that is, thunks whose computation binds type
-- variables of its own) will fail to compile.
--
-- @since 1.2.0
match ::
  forall (m :: Type -> Type).
  (MonadHashCons Id ASGNode m, MonadError CovenantTypeError m, MonadReader ASGEnv m) =>
  Ref ->
  Vector Ref ->
  m Id
match scrutinee handlers = do
  scrutNodeTy <- typeRef scrutinee
  case scrutNodeTy of
    ValNodeType scrutTy@(Datatype tn args) ->
      isRecursive scrutTy >>= \case
        True -> goRecursive tn args
        False -> goNonRecursive tn args
    ValNodeType other -> throwError $ MatchNonDatatypeScrutinee other
    other -> throwError $ MatchNonValTy other
  where
    isRecursive :: ValT AbstractTy -> m Bool
    isRecursive (Datatype tyName _) = do
      datatypeInfoExists <- asks (isJust . preview (#datatypeInfo % ix tyName))
      if datatypeInfoExists
        then asks (isJust . join . preview (#datatypeInfo % ix tyName % #baseFunctor))
        else throwError $ MatchNoDatatypeInfo tyName
    isRecursive _ = pure False

    goRecursive :: TyName -> Vector (ValT AbstractTy) -> m Id
    goRecursive tn@(TyName rawTn) tyConArgs = do
      -- This fromJust is safe b/c the presence of absence of base functor data is the condition that
      -- determines whether we're in this branch or the non-recursive one
      rawBFBB <- asks (snd . fromJust . join . preview (#datatypeInfo % ix tn % #baseFunctor))
      bfbb <- instantiateBFBB rawBFBB
      handlers' <- Vector.toList <$> traverse cleanupHandler handlers
      tyDict <- asks (view #datatypeInfo)
      case checkApp tyDict bfbb (Just <$> handlers') of
        Right appliedBfbb -> do
          result <- undoRenameM appliedBfbb
          refTo $ AValNode result (MatchInternal scrutinee handlers)
        Left err' -> throwError . UnificationError $ err'
      where
        instantiateBFBB :: ValT AbstractTy -> m (CompT Renamed)
        instantiateBFBB bfbb = do
          -- we have a BFBB like:
          -- listBB :: forall a r . r -> <a -> r -> !r> -> !r
          -- And we need to:
          --   1. Instantiate all of the type arguments to the original datatype (e.g. the 'a' in List a)
          --      into the BFBB
          --   2. Instantiate the *last* tyvar bound by the BBBF to the type of the original datatype
          --      giving us, e.g. ListF a (List a)
          scope <- askScope
          renamedBFBB <- case runRenameM scope (renameValT bfbb) of
            Left err' -> throwError $ MatchRenameBBFail err'
            Right res -> pure res
          -- The type constructor for the base-functor variant of the scrutinee type.
          let scrut = Datatype tn tyConArgs
          let scrutF = Datatype (TyName $ "#" <> rawTn) (Vector.snoc tyConArgs scrut)
          -- These are arguments to the original type constructor plus the snoc'd original type.
          -- E.g. if we have:
          --      Scrutinee: List Int
          --   this should be:
          --   [Int, List Int]
          let bfInstArgs = Vector.snoc tyConArgs scrutF
          renamedArgs <- case runRenameM scope (traverse renameValT bfInstArgs) of
            Left err' -> throwError $ MatchRenameTyConArgFail err'
            Right res -> pure res
          let subs :: Vector (Index "tyvar", ValT Renamed)
              subs = Vector.imap (\i v -> (fromJust . preview intIndex $ i, v)) renamedArgs
              subbed = foldl' (\bbf (i, v) -> substitute i v bbf) renamedBFBB subs
          case subbed of
            ThunkT bfComp -> pure bfComp
            other -> throwError $ MatchNonThunkBBF other

    -- Unwraps a thunk handler if it is a handler for a nullary constructor.
    cleanupHandler :: Ref -> m (ValT Renamed)
    cleanupHandler r =
      renameArg r >>= \case
        Nothing ->
          throwError $ MatchErrorAsHandler r
        Just hVal -> case hVal of
          hdlr@(ThunkT (CompT cnt (ReturnT v)))
            | cnt == count0 -> pure v
            | otherwise -> throwError $ MatchPolymorphicHandler hdlr
          other -> pure other

    goNonRecursive :: TyName -> Vector (ValT AbstractTy) -> m Id
    goNonRecursive tn tyConArgs = do
      rawBBF <- asks (fromJust . preview (#datatypeInfo % ix tn % #bbForm))
      (instantiatedBBF :: CompT Renamed) <- instantiateBB rawBBF tyConArgs
      handlers' <- Vector.toList <$> traverse cleanupHandler handlers
      tyDict <- asks (view #datatypeInfo)
      case checkApp tyDict instantiatedBBF (Just <$> handlers') of
        Right appliedBBF -> do
          result <- undoRenameM appliedBBF
          refTo $ AValNode result (MatchInternal scrutinee handlers)
        Left err' -> throwError . UnificationError $ err'
      where
        instantiateBB :: Maybe (ValT AbstractTy) -> Vector (ValT AbstractTy) -> m (CompT Renamed)
        instantiateBB Nothing _ = throwError $ MatchNoBBForm tn
        instantiateBB (Just bb) tyArgs = do
          scope <- askScope
          renamedBB <- case runRenameM scope (renameValT bb) of
            Left err' -> throwError $ MatchRenameBBFail err'
            Right res -> pure res
          renamedArgs <- case runRenameM scope (traverse renameValT tyArgs) of
            Left err' -> throwError $ MatchRenameTyConArgFail err'
            Right res -> pure res
          let subs :: Vector (Index "tyvar", ValT Renamed)
              subs = Vector.imap (\i v -> (fromJust . preview intIndex $ i, v)) renamedArgs
              subbed = foldl' (\bbf (i, v) -> substitute i v bbf) renamedBB subs
          case subbed of
            ThunkT bbComp -> pure bbComp
            other -> throwError $ MatchNonThunkBBF other

-- Helpers

-- Note (Koz, 13/08/2025): We need this procedure specifically for `cata`. The
-- reason for this has to do with how we construct the 'base functor form' of
-- the value to be torn down by the catamorphism, in order to use the
-- unification machinery to get the type of the final result.
--
-- To be specific, suppose we have `<#List r (Maybe r) -> !Maybe r>` as our algebra
-- argument (where `r` is some rigid), and `List r` as the value to be torn
-- down. If we assume the rigid is bound one scope away, `r`'s DeBruijn index
-- will be `S Z` for
-- the value to be torn down, but `S (S Z)` for the algebra argument. The way
-- our approach works is:
--
-- 1. Look at the algebra argument, specifically the base functor type. Take its
--    last type argument, which we will call `last`.
-- 2. Determine the base functor for the value to be torn down. Cook up a new
--    instance of the base functor type, copying all the type arguments from the
--    value to be torn down in the same order. Then put `last` at the end.
-- 3. Force the algebra argument thunk, then try and apply the result of Step 2
--    to that.
--
-- Following the steps above for our example, we would proceed as follows:
--
-- 1. Set `last` as `Maybe r`.
-- 2. Cook up `#List r (Maybe r)`. Note that this matches what the algebra
--    expects.
-- 3. Use the unifier with `#List r (Maybe r) -> !Maybe r`, applying the
--    argument `#List r (Maybe r)` from Step 2.
--
-- However, if `last` is a rigid, we have an 'off by one error'. To see why,
-- consider the form of the algebra argument:
--
-- `ThunkT . Comp0 $ Datatype "#List" [tyvar (S (S Z)) ix0, ....`
--
-- However, `tyvar (S (S Z)) ix0` is not valid in the scope of the value to be
-- torn down: that same rigid would have DeBruijn index `S Z` there instead.
-- This applies the same if the tyvar is part of a datatype.
--
-- As we prohibit non-rigid algebras, this requires us to lower the DeBruijn
-- index by one for our process.
stepDownDB :: ValT AbstractTy -> ValT AbstractTy
stepDownDB = \case
  Abstraction (BoundAt db i) -> case db of
    -- This is impossible, so we just return it unmodified
    Z -> Abstraction (BoundAt db i)
    (S db') -> Abstraction (BoundAt db' i)
  Datatype tyName tyArgs -> Datatype tyName . fmap stepDownDB $ tyArgs
  x -> x

renameArg ::
  forall (m :: Type -> Type).
  (MonadHashCons Id ASGNode m, MonadError CovenantTypeError m, MonadReader ASGEnv m) =>
  Ref ->
  m (Maybe (ValT Renamed))
renameArg r =
  askScope >>= \scope ->
    typeRef r >>= \case
      CompNodeType t -> throwError . ApplyCompType $ t
      ValNodeType t -> case runRenameM scope . renameValT $ t of
        Left err' -> throwError . RenameArgumentFailed t $ err'
        Right renamed -> pure . Just $ renamed
      ErrorNodeType -> pure Nothing

checkEncodingWithInfo ::
  forall (a :: Type) (m :: Type -> Type).
  (MonadError CovenantTypeError m) =>
  Map TyName (DatatypeInfo a) ->
  ValT AbstractTy ->
  m ()
checkEncodingWithInfo tyDict valT = case checkEncodingArgs (view (#originalDecl % #datatypeEncoding)) tyDict valT of
  Left encErr -> throwError $ EncodingError encErr
  Right {} -> pure ()

tryApply ::
  forall (m :: Type -> Type).
  (MonadError CovenantTypeError m, MonadReader ASGEnv m) =>
  CompT AbstractTy ->
  ValT AbstractTy ->
  m (ValT AbstractTy)
tryApply algebraT argT =
  askScope >>= \scope -> case runRenameM scope . renameCompT $ algebraT of
    Left err' -> throwError . RenameFunctionFailed algebraT $ err'
    Right renamedAlgebraT -> case runRenameM scope . renameValT $ argT of
      Left err' -> throwError . RenameArgumentFailed argT $ err'
      Right renamedArgT -> do
        tyDict <- asks (view #datatypeInfo)
        case checkApp tyDict renamedAlgebraT [Just renamedArgT] of
          Left err' -> throwError . UnificationError $ err'
          Right resultT -> undoRenameM resultT

-- Putting this here to reduce chance of annoying manual merge (will move later)

-- | Given a DeBruijn index (designating scope) and positional index (designating
-- which variable in that scope we are interested in), retrieve an in-scope type
-- variable.
--
-- This will error if we request a type variable in a scope that doesn't exist,
-- or at a position that doesn't exist in that scope.
--
-- @since 1.2.0
boundTyVar ::
  forall (m :: Type -> Type).
  (MonadError CovenantTypeError m, MonadReader ASGEnv m) =>
  DeBruijn ->
  Index "tyvar" ->
  m BoundTyVar
boundTyVar scope index = do
  let scopeAsInt = review asInt scope
      indexAsWord :: Word32
      indexAsWord = fromIntegral $ review intIndex index
  tyVarInScope <-
    asks (preview (#scopeInfo % #argumentInfo % ix scopeAsInt % _1)) >>= \case
      Nothing -> pure False
      Just varsBoundAtScope ->
        -- varsBoundAtScope is the count of the CompT binding context verbatim
        if varsBoundAtScope <= 0
          then pure False
          else pure $ indexAsWord < varsBoundAtScope
  if tyVarInScope
    then pure (BoundTyVar scope index)
    else throwError $ OutOfScopeTyVar scope index

-- To avoid annoying code duplication

-- Helper to avoid having to manually catch and rethrow the error
undoRenameM ::
  forall (m :: Type -> Type).
  (MonadError CovenantTypeError m, MonadReader ASGEnv m) =>
  ValT Renamed ->
  m (ValT AbstractTy)
undoRenameM val = do
  scope <- asks (fmap fst . view (#scopeInfo % #argumentInfo))
  case undoRename scope val of
    Left err' -> throwError $ UndoRenameFailure err'
    Right renamed -> pure renamed

askScope ::
  forall (m :: Type -> Type).
  (MonadReader ASGEnv m) =>
  m (Vector Word32)
askScope = asks (fmap fst . view (#scopeInfo % #argumentInfo))

-- Runs a UnifyM computation in our abstract monad. Again, largely to avoid superfluous code
-- duplication.
liftUnifyM ::
  forall (m :: Type -> Type) (a :: Type).
  (MonadHashCons Id ASGNode m, MonadError CovenantTypeError m, MonadReader ASGEnv m) =>
  UnifyM a ->
  m a
liftUnifyM act = do
  tyDict <- asks (view #datatypeInfo)
  case runUnifyM tyDict act of
    Left e -> throwError $ UnificationError e
    Right res -> pure res

-- Utility functions for ASG construction. These are not strictly necessary, but are extremely convenient.

-- | Constructs a datatype value at given constructor. This is different to
-- 'dataConstructor', as it doesn't produce a thunk.
--
-- The third argument is a 'Vector' of values to \'fill in\' all the fields
-- required by the stated constructor. The fourth argument is a 'Vector' of
-- \'type instantiations\', which allow \'concretification\' of any lingering
-- polymorphic type variables which are not determined by the field values given
-- as the third argument.
--
-- = Example
--
-- Consider @Left 3@. In this case, the field only determines the first type
-- argument to the @Either@ data type, and if we used 'dataConstructor', we
-- would be left with a thunk of type @<forall a . !Either Integer a>@. Using
-- 'ctor', we can immediately specify what @a@ should be, and unwrap the thunk.
--
-- @since 1.2.0
ctor ::
  forall (m :: Type -> Type).
  (MonadHashCons Id ASGNode m, MonadError CovenantTypeError m, MonadReader ASGEnv m) =>
  TyName ->
  ConstructorName ->
  Vector.Vector Ref ->
  Vector.Vector (Wedge BoundTyVar (ValT Void)) ->
  m Id
ctor tn cn args instTys = do
  dataThunk <- dataConstructor tn cn args
  dataForced <- force (AnId dataThunk)
  app dataForced mempty instTys

-- | 'ctor' without the instantiation arguments, which are left up to inference.
-- @since 1.3.0
ctor' ::
  forall (m :: Type -> Type).
  (MonadHashCons Id ASGNode m, MonadError CovenantTypeError m, MonadReader ASGEnv m) =>
  TyName ->
  ConstructorName ->
  Vector.Vector Ref ->
  m Id
ctor' tn cn args = do
  dataThunk <- dataConstructor tn cn args
  dataForced <- force (AnId dataThunk)
  app' dataForced mempty

-- | A variant of `app` which does not take a vector of type instantiation arguments and
--   attempts to infer all type variables.
-- @since 1.3.0
app' ::
  forall (m :: Type -> Type).
  (MonadHashCons Id ASGNode m, MonadError CovenantTypeError m, MonadReader ASGEnv m) =>
  Id ->
  Vector Ref ->
  m Id
app' fId args =
  typeId fId >>= \case
    CompNodeType (CompT count _) -> do
      let numVars = review intCount count
          instArgs = Vector.replicate numVars Nowhere
      app fId args instArgs
    ValNodeType t -> throwError . ApplyToValType $ t
    ErrorNodeType -> throwError ApplyToError

-- | As 'lam', but produces a thunk value instead of a computation.
--
-- @since 1.2.0
lazyLam ::
  forall (m :: Type -> Type).
  (MonadHashCons Id ASGNode m, MonadError CovenantTypeError m, MonadReader ASGEnv m) =>
  CompT AbstractTy ->
  m Ref ->
  m Id
lazyLam expected bodyComp = lam expected bodyComp >>= thunk

-- | Helper to avoid using 'Vector.fromList' when defining data types.
--
-- @since 1.2.0
dtype :: TyName -> [ValT AbstractTy] -> ValT AbstractTy
dtype tn = Datatype tn . Vector.fromList

-- | Helper for constructing a base functor name without having know the internal naming convention for
--   base functors.
--
-- @since 1.3.0
baseFunctorOf ::
  forall (m :: Type -> Type).
  (MonadError CovenantTypeError m, MonadReader ASGEnv m) =>
  TyName ->
  m TyName
baseFunctorOf (TyName tn) = do
  let bfTn = TyName ("#" <> tn)
  tyDict <- asks (view #datatypeInfo)
  case preview (ix bfTn) tyDict of
    Nothing -> throwError $ BaseFunctorDoesNotExistFor (TyName tn)
    Just {} -> pure bfTn

-- Hardcoded constants for Integer base functors.
-- Integer is the only type that has TWO base functors and so
-- its base functor cannot be determined from its type alone.

-- | The name of the Natural base functor for Integer.
-- Integer is the only type that has TWO base functors and so
-- its base functor cannot be determined from its type name alone.
-- @since 1.3.0
naturalBF :: TyName
naturalBF = TyName "#Natural"

-- | The name of the Negative base functor for Integer
-- Integer is the only type that has TWO base functors and so
-- its base functor cannot be determined from its type name alone.
-- @since 1.3.0
negativeBF :: TyName
negativeBF = TyName "#Negative"
