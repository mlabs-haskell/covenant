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
module Covenant.Internal.KindCheck (checkKinds, KindCheckError (..), cycleCheck) where

import Control.Monad (unless)
import Control.Monad.Except (ExceptT, MonadError (throwError), runExceptT)
import Control.Monad.Reader (MonadReader (local), ReaderT (ReaderT), asks, runReaderT)
import Covenant.Index (Count, intCount)
import Covenant.Internal.Type
  ( AbstractTy,
    CompT (CompT),
    CompTBody (CompTBody),
    DataDeclaration (DataDeclaration, OpaqueData),
    TyName,
    ValT (Abstraction, BuiltinFlat, Datatype, ThunkT), Constructor (Constructor), datatype,
  )
import Data.Foldable (traverse_)
import Data.Functor.Identity (Identity, runIdentity)
import Data.Kind (Type)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as M
import Data.Vector (Vector)
import Data.Vector qualified as V
import Optics.Core (A_Lens, LabelOptic (labelOptic), lens, review, view, preview, to, (%))
import Data.Set (Set)
import Data.Set qualified as Set
import Covenant.Data (everythingOf)
import Data.Maybe (mapMaybe)

data KindCheckError
  = UnknownType TyName
  | IncorrectNumArgs TyName (Count "tyvar") (Vector (ValT AbstractTy)) -- first is expected (from the decl), second is actual
  | HigherOrderConstructorArg (CompT AbstractTy) -- no polymorphic function args to ctors
  | MutualRecursionDetected (Set TyName)
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

runKindCheckM :: forall (t :: Type) (a :: Type). KindCheckM t a -> Either KindCheckError a
runKindCheckM (KindCheckM act) = runIdentity . runExceptT $ runReaderT act (KindCheckContext M.empty)

lookupDeclaration :: forall (t :: Type). TyName -> KindCheckM t (DataDeclaration t)
lookupDeclaration tn = do
  types <- asks (view #kindCheckContext)
  case M.lookup tn types of
    Nothing -> throwError $ UnknownType tn
    Just decl -> pure decl

-- This isn't really a "kind checker" in the normal sense and just checks that none of the three failure conditions above obtain
checkKinds' :: ValT AbstractTy -> KindCheckM AbstractTy ()
checkKinds' = \case
  Abstraction _ -> pure ()
  ThunkT compT@(CompT cnt (CompTBody nev)) -> case review intCount cnt of
    0 -> traverse_ checkKinds' nev
    _ -> throwError $ HigherOrderConstructorArg compT -- no higher order arguments to ctors (makes life much easier, not that useful)
  BuiltinFlat {} -> pure ()
  Datatype tn args -> lookupDeclaration tn >>= \case
    OpaqueData{} -> pure () 
    DataDeclaration _ numVars _ _ -> do
      let numArgsActual = V.length args
          numArgsExpected = review intCount numVars
      unless (numArgsActual == numArgsExpected) $ throwError (IncorrectNumArgs tn numVars args)
      traverse_ checkKinds' args

checkKinds :: ValT AbstractTy -> Maybe KindCheckError
checkKinds = either Just (const Nothing) . runKindCheckM . checkKinds'

-- Ensures that we don't have any *mutually* recursive datatypes (which we don't want b/c they mess with data encoding strategies)
cycleCheck :: forall (a :: Type). Ord a => Map TyName (DataDeclaration a) -> Maybe KindCheckError
cycleCheck decls = either Just (const Nothing) $ runKindCheckM go
  where
    go = local (\_ -> KindCheckContext decls) $ 
      traverse_ (cycleCheck' Set.empty) =<< asks (view (#kindCheckContext % to M.elems))


{- This is a bit odd b/c we don't want to fail for auto-recursive types, so we need to be careful
   *not* to mark the current decl being examined as "visited" until we've "descended" into the dependencies
   (I think?)
-}
cycleCheck' :: forall (a :: Type). Ord a => Set TyName -> DataDeclaration a -> KindCheckM a ()
cycleCheck' _ OpaqueData{} = pure ()
cycleCheck' visited (DataDeclaration tn _ ctors _) = traverse_ (checkCtor visited tn) ctors
  where
    checkCtor :: Set TyName -> TyName -> Constructor a -> KindCheckM a ()
    checkCtor vs tn' (Constructor _ args) = do
      let allComponents =  Set.toList . Set.unions $ everythingOf <$> V.toList args
          -- every type constructor in any part of a constructor arg, *except* the tycon of the decl
          -- we're examining, since autorecursion is fine/necessary
          allTyCons  = Set.filter (/= tn') . Set.fromList . mapMaybe (fmap fst . preview datatype) $ allComponents
          alreadyVisitedArgTys = Set.intersection allTyCons vs
      unless (null alreadyVisitedArgTys) $ throwError (MutualRecursionDetected alreadyVisitedArgTys)
      let newVisited = Set.insert tn' vs
      nextRound <- traverse lookupDeclaration (Set.toList allTyCons)
      traverse_ (cycleCheck' newVisited) nextRound
