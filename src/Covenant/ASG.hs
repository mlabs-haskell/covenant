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
    ASG,

    -- ** Functions
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
        Force,
        Return
      ),
    ValNodeInfo (Lit, App, Thunk, Cata),
    ASGNode (..),

    -- ** Functions
    typeASGNode,

    -- * ASG builder

    -- ** Types
    CovenantError (..),
    ScopeInfo,
    ASGBuilder,
    TypeAppError (..),
    RenameError (..),
    CovenantTypeError (..),
    BoundTyVar, -- I don't think we need to, or should, export the constructor.

    -- ** Introducers
    arg,
    builtin1,
    builtin2,
    builtin3,
    builtin6,
    force,
    ret,
    lam,
    err,
    lit,
    thunk,
    app,
    cata,
    boundTyVar,

    -- ** Elimination

    -- *** Environment
    defaultDatatypes,

    -- *** Function
    runASGBuilder,
  )
where

import Control.Monad (unless)
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
import Covenant.Data (DatatypeInfo, mkDatatypeInfo)
import Covenant.DeBruijn (DeBruijn, asInt)
import Covenant.Index (Index, count0, intIndex)
import Covenant.Internal.KindCheck (checkEncodingArgs)
import Covenant.Internal.Ledger (ledgerTypes)
import Covenant.Internal.Rename
  ( RenameError
      ( InvalidAbstractionReference
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
        Builtin6Internal,
        ForceInternal,
        LamInternal,
        ReturnInternal
      ),
    CovenantTypeError
      ( ApplyCompType,
        ApplyToError,
        ApplyToValType,
        BrokenIdReference,
        CataApplyToNonValT,
        CataNotAnAlgebra,
        CataUnsuitable,
        CataWrongBuiltinType,
        CataWrongValT,
        EncodingError,
        ForceCompType,
        ForceError,
        ForceNonThunk,
        LambdaResultsInNonReturn,
        LambdaResultsInValType,
        NoSuchArgument,
        OutOfScopeTyVar,
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
    Ref (AnArg, AnId),
    ValNodeInfo (AppInternal, CataInternal, LitInternal, ThunkInternal),
    typeASGNode,
    typeId,
    typeRef,
  )
import Covenant.Internal.Type
  ( AbstractTy,
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
    checkApp,
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
import Data.Bimap (Bimap)
import Data.Bimap qualified as Bimap
import Data.Coerce (coerce)
import Data.Functor.Identity (Identity, runIdentity)
import Data.Kind (Type)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe (fromJust, isJust)
import Data.Vector (Vector)
import Data.Vector qualified as Vector
import Data.Vector.NonEmpty qualified as NonEmpty
import Optics.Core
  ( A_Lens,
    LabelOptic (labelOptic),
    at,
    ix,
    lens,
    over,
    preview,
    review,
    view,
    (%),
  )


-- | A fully-assembled Covenant ASG.
--
-- @since 1.0.0
newtype ASG = ASG (Id, Map Id ASGNode)
  deriving stock
    ( -- | @since 1.0.0
      Eq,
      -- | @since 1.0.0
      Show
    )

-- Note (Koz, 24/04/25): The `topLevelNode` and `nodeAt` functions use `fromJust`,
-- because we can guarantee it's impossible to miss. For an end user, the only
-- way to get hold of an `Id` is by inspecting a node, and since we control how
-- these are built and assigned, and users can't change them, it's safe.
--
-- It is technically possible to escape this safety regime by having two
-- different `ASG`s and mixing up their `Id`s. However, this is both vanishingly
-- unlikely and probably not worth trying to protect against, given the nuisance
-- of having to work in `Maybe` all the time.

-- | Retrieves the top-level node of an ASG.
--
-- @since 1.0.0
topLevelNode :: ASG -> ASGNode
topLevelNode asg@(ASG (rootId, _)) = nodeAt rootId asg

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
nodeAt i (ASG (_, mappings)) = fromJust . Map.lookup i $ mappings

data ASGEnv = ASGEnv ScopeInfo (Map TyName (DatatypeInfo AbstractTy))

instance
  (k ~ A_Lens, a ~ ScopeInfo, b ~ ScopeInfo) =>
  LabelOptic "scopeInfo" k ASGEnv ASGEnv a b
  where
  {-# INLINEABLE labelOptic #-}
  labelOptic =
    lens
      (\(ASGEnv si _) -> si)
      (\(ASGEnv _ dti) si -> ASGEnv si dti)

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
-- @since 1.0.0
newtype ScopeInfo = ScopeInfo (Vector (Vector (ValT AbstractTy)))
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
-- @since 1.0.0
instance
  (k ~ A_Lens, a ~ Vector (Vector (ValT AbstractTy)), b ~ Vector (Vector (ValT AbstractTy))) =>
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

-- | Produce the result of a computation.
--
-- @since 1.0.0
pattern Return :: Ref -> CompNodeInfo
pattern Return r <- ReturnInternal r

-- | A lambda.
--
-- @since 1.0.0
pattern Lam :: Id -> CompNodeInfo
pattern Lam i <- LamInternal i

{-# COMPLETE Builtin1, Builtin2, Builtin3, Builtin6, Force, Return, Lam #-}

-- | A compile-time literal of a flat builtin type.
--
-- @since 1.0.0
pattern Lit :: AConstant -> ValNodeInfo
pattern Lit c <- LitInternal c

-- | An application of a computation (the 'Id' field) to some arguments (the
-- 'Vector' field).
--
-- @since 1.0.0
pattern App :: Id -> Vector Ref -> ValNodeInfo
pattern App f args <- AppInternal f args

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

{-# COMPLETE Lit, App, Thunk, Cata #-}

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
defaultDatatypes = foldMap go ledgerTypes
  where
    go :: DataDeclaration AbstractTy -> Map TyName (DatatypeInfo AbstractTy)
    go decl = case mkDatatypeInfo decl of
      Left err' -> error $ "Unexpected failure in default datatypes: " <> show err'
      Right info -> Map.singleton (view #datatypeName decl) info

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
            ACompNode _ _ -> pure . ASG $ (i, Bimap.toMap bm)
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
  lookedUp <- asks (preview (#scopeInfo % #argumentInfo % ix scopeAsInt % ix indexAsInt))
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

-- | Given the result of a function body (either a value or an error), construct
-- the return for it. Will fail if that reference aims at a computation node.
--
-- @since 1.0.0
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
-- the argument being passed is an @m Id@.
--
-- @since 1.0.0
lam ::
  forall (m :: Type -> Type).
  (MonadHashCons Id ASGNode m, MonadError CovenantTypeError m, MonadReader ASGEnv m) =>
  CompT AbstractTy ->
  m Id ->
  m Id
lam expectedT@(CompT _ (CompTBody xs)) bodyComp = do
  let (args, resultT) = NonEmpty.unsnoc xs
  bodyId <- local (over (#scopeInfo % #argumentInfo) (Vector.cons args)) bodyComp
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
          ErrorNodeType -> throwError ReturnWrapsError -- Should be impossible
          CompNodeType t' -> throwError . ReturnWrapsCompType $ t'
      _ -> throwError . LambdaResultsInNonReturn $ t
    Just (AValNode t _) -> throwError . LambdaResultsInValType $ t

-- | Construct the error node.
--
-- @since 1.0.0
err ::
  forall (m :: Type -> Type).
  (MonadHashCons Id ASGNode m) =>
  m Id
err = refTo AnError

-- | Given an 'Id' referring to a computation, and a 'Vector' of 'Ref's to the
-- desired arguments, construct the application of the arguments to that
-- computation. This can fail for a range of reasons:
--
-- * Type mismatch between what the computation expects and what it's given
-- * Too many or too few arguments
-- * Not a computation type for 'Id' argument
-- * Not value types for 'Ref's
--
-- @since 1.0.0
app ::
  forall (m :: Type -> Type).
  (MonadHashCons Id ASGNode m, MonadError CovenantTypeError m, MonadReader ASGEnv m) =>
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
        tyDict <- asks (view #datatypeInfo)
        result <- either (throwError . UnificationError) pure $ checkApp tyDict renamedFT (Vector.toList renamedArgs)
        let restored = undoRename result
        checkEncodingWithInfo tyDict restored
        refTo . AValNode restored . AppInternal fId $ argRefs
    ValNodeType t -> throwError . ApplyToValType $ t
    ErrorNodeType -> throwError ApplyToError

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
        t@(ValNodeType (ThunkT algT@(CompT _ (CompTBody nev)))) -> do
          unless (arity algT == 2) (throwError . CataNotAnAlgebra $ t)
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
              let lastVar = Vector.last bfTyArgs
              unless (nev NonEmpty.! 1 == lastVar) (throwError . CataNotAnAlgebra $ t)
              appliedArgT <- case valT of
                BuiltinFlat bT -> case bT of
                  ByteStringT -> do
                    unless (bfName == "ByteString_F") (throwError . CataUnsuitable algT $ valT)
                    pure $ Datatype "ByteString_F" . Vector.singleton $ lastVar
                  IntegerT -> do
                    let isSuitableBaseFunctor = bfName == "Natural_F" || bfName == "Negative_F"
                    unless isSuitableBaseFunctor (throwError . CataUnsuitable algT $ valT)
                    pure $ Datatype bfName . Vector.singleton $ lastVar
                  _ -> throwError . CataWrongBuiltinType $ bT
                Datatype tyName tyVars -> do
                  lookedUp <- asks (view (#datatypeInfo % at tyName))
                  case lookedUp of
                    Nothing -> throwError . CataUnsuitable algT $ valT
                    Just info -> case view #baseFunctor info of
                      Just (DataDeclaration actualBfName _ _ _, _) -> do
                        unless (bfName == actualBfName) (throwError . CataUnsuitable algT $ valT)
                        pure . Datatype bfName . Vector.snoc tyVars $ lastVar
                      _ -> throwError . CataUnsuitable algT $ valT
                _ -> throwError . CataWrongValT $ valT
              resultT <- tryApply algT appliedArgT
              refTo . AValNode resultT . CataInternal rAlg $ rVal
            _ -> throwError . CataNotAnAlgebra $ t
        t -> throwError . CataNotAnAlgebra $ t
    t -> throwError . CataApplyToNonValT $ t

-- Helpers

renameArg ::
  forall (m :: Type -> Type).
  (MonadHashCons Id ASGNode m, MonadError CovenantTypeError m) =>
  Ref ->
  m (Maybe (ValT Renamed))
renameArg r =
  typeRef r >>= \case
    CompNodeType t -> throwError . ApplyCompType $ t
    ValNodeType t -> case runRenameM . renameValT $ t of
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
tryApply algebraT argT = case runRenameM . renameCompT $ algebraT of
  Left err' -> throwError . RenameFunctionFailed algebraT $ err'
  Right renamedAlgebraT -> case runRenameM . renameValT $ argT of
    Left err' -> throwError . RenameArgumentFailed argT $ err'
    Right renamedArgT -> do
      tyDict <- asks (view #datatypeInfo)
      case checkApp tyDict renamedAlgebraT [Just renamedArgT] of
        Left err' -> throwError . UnificationError $ err'
        Right resultT -> pure . undoRename $ resultT

-- Putting this here to reduce chance of annoying manual merge (will move later)

-- | Wrapper around an `Arg` that we know represents an in-scope type variable.
-- @since 1.2.0
data BoundTyVar = BoundTyVar DeBruijn (Index "tyvar")
  deriving stock
    ( -- @since 1.2.0
      Show,
      -- @since 1.2.0
      Eq,
      -- @since 1.2.0
      Ord
    )
-- | Given a DB Index and position index, safely retrieve an in-scope type variable.
-- @since 1.2.0
boundTyVar ::
  forall (m :: Type -> Type).
  (MonadError CovenantTypeError m, MonadReader ASGEnv m) =>
  DeBruijn ->
  Index "tyvar" ->
  m BoundTyVar
boundTyVar scope index = do
  let scopeAsInt = review asInt scope
  let indexAsInt = review intIndex index
  tyVarInScope <- asks (isJust . preview (#scopeInfo % #argumentInfo % ix scopeAsInt % ix indexAsInt))
  if tyVarInScope
    then pure (BoundTyVar scope index)
    else throwError $ OutOfScopeTyVar scope index
