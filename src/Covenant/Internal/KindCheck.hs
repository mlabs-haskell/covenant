-- | This module define a "kind-checking" pass. This requires some explanation, since we don't have
--     an *explicit* notion of kinds in Covenant:
--
--     With the addition of type constructors for datatypes into ValT comes a new set of things that can
--     "go wrong". In particular:
--       - Someone may try to use a type constructor which is not defined anywhere
--       - A type may be applied to an incorrect number of arguments
--       - The "count" - the number of bound tyvars in the `ValT.Datatype` representation - may be incorrect (i.e. inconsistent with the count in the declaration)
--
--     The checks to detect these errors are entirely independent from the checks performed during typechecking or renaming, so we do them in a separate pass.
module Covenant.Internal.KindCheck (checkDataDecls, checkValT, KindCheckError (..), EncodingArgErr (..), cycleCheck, checkEncodingArgs) where

import Control.Monad (unless)
import Control.Monad.Except (ExceptT, MonadError (throwError), runExceptT)
import Control.Monad.Reader (MonadReader (local), ReaderT (ReaderT), asks, runReaderT)
import Covenant.Data (everythingOf)
import Covenant.Index (Count, intCount)
import Covenant.Internal.Type
  ( AbstractTy,
    CompT (CompT),
    CompTBody (CompTBody),
    Constructor (Constructor),
    DataDeclaration (DataDeclaration, OpaqueData),
    DataEncoding (SOP),
    TyName,
    ValT (Abstraction, BuiltinFlat, Datatype, ThunkT),
    checkStrategy,
    datatype,
  )
import Data.Foldable (traverse_)
import Data.Functor.Identity (Identity, runIdentity)
import Data.Kind (Type)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as M
import Data.Maybe (mapMaybe)
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Vector (Vector)
import Data.Vector qualified as V
import Optics.Core (A_Lens, LabelOptic (labelOptic), folded, lens, preview, review, to, toListOf, view, (%))

{- TODO: Explicitly separate the kind checker into two check functions:
     - One which kind checks `ValT`s to ensure:
       1. All TyCons in the ValT exist
       2. All TyCons in the ValT have the correct arity

     - One which checks *datatype declarations* to ensure:
       1. Everything satisfies the above ValT checks
       2. No thunk arguments to ctors!
       3. No mutual recursion (cycles)
-}

data KindCheckError
  = UnknownType TyName
  | IncorrectNumArgs TyName (Count "tyvar") (Vector (ValT AbstractTy)) -- first is expected (from the decl), second is actual
  | ThunkConstructorArg (CompT AbstractTy) -- no polymorphic function args to ctors
  | MutualRecursionDetected (Set TyName)
  | InvalidStrategy TyName
  | EncodingMismatch (EncodingArgErr AbstractTy)
  deriving stock (Show, Eq)

newtype KindCheckContext a = KindCheckContext (Map TyName (DataDeclaration a))

instance
  (k ~ A_Lens, a ~ Map TyName (DataDeclaration c), b ~ Map TyName (DataDeclaration c)) =>
  LabelOptic "kindCheckContext" k (KindCheckContext c) (KindCheckContext c) a b
  where
  {-# INLINEABLE labelOptic #-}
  labelOptic =
    lens
      (\(KindCheckContext x) -> x)
      (\(KindCheckContext _) x' -> KindCheckContext x')

newtype KindCheckM t a = KindCheckM (ReaderT (KindCheckContext t) (ExceptT KindCheckError Identity) a)
  deriving
    (Functor, Applicative, Monad, MonadReader (KindCheckContext t), MonadError KindCheckError)
    via (ReaderT (KindCheckContext t) (ExceptT KindCheckError Identity))

runKindCheckM :: forall (t :: Type) (a :: Type). Map TyName (DataDeclaration t) -> KindCheckM t a -> Either KindCheckError a
runKindCheckM dtypes (KindCheckM act) = runIdentity . runExceptT $ runReaderT act (KindCheckContext dtypes)

lookupDeclaration :: forall (t :: Type). TyName -> KindCheckM t (DataDeclaration t)
lookupDeclaration tn = do
  types <- asks (view #kindCheckContext)
  case M.lookup tn types of
    Nothing -> throwError $ UnknownType tn
    Just decl -> pure decl

{- This sanity checks datatype declarations using the criteria enumerated above.

-}

checkDataDecls :: Map TyName (DataDeclaration AbstractTy) -> Either KindCheckError ()
checkDataDecls decls = runKindCheckM decls $ traverse_ checkDataDecl (M.elems decls)

checkDataDecl :: DataDeclaration AbstractTy -> KindCheckM AbstractTy ()
checkDataDecl OpaqueData {} = pure ()
checkDataDecl decl@(DataDeclaration tn _ ctors _) = do
  unless (checkStrategy decl) $ throwError (InvalidStrategy tn)
  cycleCheck' mempty decl
  let allCtorArgs = view #constructorArgs =<< ctors
  traverse_ (checkKinds CheckDataDecl) allCtorArgs
  checkEncodingArgsInDataDecl decl

data KindCheckMode = CheckDataDecl | CheckValT
  deriving stock (Show, Eq, Ord)

-- This isn't really a "kind checker" in the normal sense and just checks that none of the three failure conditions above obtain
checkKinds :: KindCheckMode -> ValT AbstractTy -> KindCheckM AbstractTy ()
checkKinds mode = \case
  Abstraction _ -> pure ()
  ThunkT compT@(CompT _ (CompTBody nev))
    | mode == CheckDataDecl -> throwError $ ThunkConstructorArg compT
    | otherwise -> traverse_ (checkKinds mode) nev
  BuiltinFlat {} -> pure ()
  Datatype tn args ->
    lookupDeclaration tn >>= \case
      OpaqueData {} -> pure ()
      DataDeclaration _ numVars _ _ -> do
        let numArgsActual = V.length args
            numArgsExpected = review intCount numVars
        unless (numArgsActual == numArgsExpected) $ throwError (IncorrectNumArgs tn numVars args)
        traverse_ (checkKinds mode) args

-- | This is for checking type annotations in the ASG, *not* datatypes
checkValT :: Map TyName (DataDeclaration AbstractTy) -> ValT AbstractTy -> Maybe KindCheckError
checkValT dtypes = either Just (const Nothing) . runKindCheckM dtypes . checkKinds CheckValT

-- Ensures that we don't have any *mutually* recursive datatypes (which we don't want b/c they mess with data encoding strategies)
cycleCheck :: forall (a :: Type). (Ord a) => Map TyName (DataDeclaration a) -> Maybe KindCheckError
cycleCheck decls = either Just (const Nothing) $ runKindCheckM decls go
  where
    go =
      local (\_ -> KindCheckContext decls) $
        traverse_ (cycleCheck' mempty) =<< asks (view (#kindCheckContext % to M.elems))

{- This is a bit odd b/c we don't want to fail for auto-recursive types, so we need to be careful
   *not* to mark the current decl being examined as "visited" until we've "descended" into the dependencies
   (I think?)

-}
cycleCheck' :: forall (a :: Type). (Ord a) => Set TyName -> DataDeclaration a -> KindCheckM a ()
cycleCheck' _ OpaqueData {} = pure ()
cycleCheck' visited (DataDeclaration tn _ ctors _) = traverse_ (checkCtor visited tn) ctors
  where
    checkCtor :: Set TyName -> TyName -> Constructor a -> KindCheckM a ()
    checkCtor vs tn' (Constructor _ args) = do
      let allComponents = Set.toList . Set.unions $ everythingOf <$> V.toList args
          -- every type constructor in any part of a constructor arg, *except* the tycon of the decl
          -- we're examining, since autorecursion is fine/necessary
          allTyCons = Set.filter (/= tn') . Set.fromList . mapMaybe (fmap fst . preview datatype) $ allComponents
          alreadyVisitedArgTys = Set.intersection allTyCons vs
      unless (null alreadyVisitedArgTys) $ throwError (MutualRecursionDetected alreadyVisitedArgTys)
      let newVisited = Set.insert tn' vs
      nextRound <- traverse lookupDeclaration (Set.toList allTyCons)
      traverse_ (cycleCheck' newVisited) nextRound

{- Arguably the closest thing to a real kind checker in the module.

   Checks whether the arguments to type constructors (ValT 'Datatype's) conform with their encoding.

-}

-- First arg is the name of the type constructor w/ a bad argument, second arg is the bad argument.
data EncodingArgErr a = EncodingArgMismatch TyName (ValT a)
  deriving stock (Show, Eq)

-- NOTE: This assumes that we've already checked that all of the relevant types *exist* in the datatype context.
--       So, if we use this to validate data declarations, we need to make sure it happens *after* the checks that
--       ensure that.
checkEncodingArgs ::
  forall (a :: Type) (info :: Type).
  (info -> DataEncoding) -> -- this lets us not care about whether we're doing this w/ a DataDeclaration or DatatypeInfo
  Map TyName info ->
  ValT a ->
  Either (EncodingArgErr a) ()
checkEncodingArgs getEncoding tyDict = \case
  Abstraction {} -> pure ()
  BuiltinFlat {} -> pure ()
  ThunkT (CompT _ (CompTBody args)) -> traverse_ go args
  Datatype tn args -> do
    let encoding = getEncoding $ tyDict M.! tn
    case encoding of
      -- Might as well check all the way down
      SOP -> traverse_ go args
      -- Both explicit data encodings and builtins should be "morally data encoded"
      _ -> do
        traverse_ go args
        traverse_ (isValidDataArg tn) args
  where
    go :: ValT a -> Either (EncodingArgErr a) ()
    go = checkEncodingArgs getEncoding tyDict

    isValidDataArg :: TyName -> ValT a -> Either (EncodingArgErr a) ()
    isValidDataArg tn = \case
      Abstraction {} -> pure ()
      BuiltinFlat {} -> pure ()
      thunk@ThunkT {} -> throwError $ EncodingArgMismatch tn thunk
      dt@(Datatype tn' args') -> do
        let encoding = getEncoding $ tyDict M.! tn'
        case encoding of
          SOP -> throwError $ EncodingArgMismatch tn dt
          _ -> traverse_ go args'

checkEncodingArgsInDataDecl :: DataDeclaration AbstractTy -> KindCheckM AbstractTy ()
checkEncodingArgsInDataDecl decl =
  asks (view #kindCheckContext) >>= \tyDict ->
    case traverse (checkEncodingArgs (view #datatypeEncoding) tyDict) allConstructorArgs of
      Left encErr -> throwError $ EncodingMismatch encErr
      Right _ -> pure ()
  where
    allConstructorArgs :: Vector (ValT AbstractTy)
    allConstructorArgs = V.concat $ toListOf (#datatypeConstructors % folded % #constructorArgs) decl
