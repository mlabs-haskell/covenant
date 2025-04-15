{- | This module define a "kind-checking" pass. This requires some explanation, since we don't have
     an *explicit* notion of kinds in Covenant:

     With the addition of type constructors for datatypes into ValT comes a new set of things that can
     "go wrong". In particular:
       - Someone may try to use a type constructor which is not defined anywhere
       - A type may be applied to an incorrect number of arguments
       - The "count" - the number of bound tyvars in the `ValT.Datatype` representation - may be incorrect (i.e. inconsistent with the count in the declaration)

     The checks to detect these errors are entirely independent from the checks performed during typechecking or renaming, so we do them in a separate pass.
-}

module Covenant.Internal.KindCheck where

import Covenant.Internal.Type
import Data.Functor.Identity 
import Covenant.Index
import Control.Monad 
import Control.Monad.Reader
import Control.Monad.Except
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as M
import Data.Vector (Vector)
import Data.Vector qualified as V
import Optics.Core
import Data.Kind (Type)
import Data.Foldable (traverse_)

data KindCheckError
  = UnknownType TyName
  | IncorrectNumArgs TyName (Count "tyvar") (Vector (ValT AbstractTy)) -- first is expected (from the decl), second is actual
  deriving stock (Show, Eq)

newtype KindCheckContext a = KindCheckContext (Map TyName (DataDeclaration a))

instance
  (k ~ A_Lens, a ~ Map TyName (DataDeclaration c), b ~ Map TyName (DataDeclaration c)) =>
  LabelOptic "kindCheckContext" k (KindCheckContext c) (KindCheckContext c) a b
  where
  {-# INLINEABLE labelOptic #-}
  labelOptic = lens (\(KindCheckContext x) -> x)
                    (\(KindCheckContext _) x' -> KindCheckContext x')

newtype KindCheckM t a = KindCheckM (ReaderT (KindCheckContext t) (ExceptT KindCheckError Identity) a)
  deriving (Functor, Applicative, Monad, MonadReader (KindCheckContext t), MonadError KindCheckError)
    via (ReaderT (KindCheckContext t) (ExceptT KindCheckError Identity))

lookupDeclaration :: forall (t :: Type). TyName -> KindCheckM t (DataDeclaration t)
lookupDeclaration tn = do
  types <- asks (view #kindCheckContext)
  case M.lookup tn types of
    Nothing -> throwError $ UnknownType tn
    Just decl -> pure decl

-- TODO: I think we need a `CompT` version as well?
-- REVIEW: This happens *before* renaming, right?
-- This isn't really a "kind checker" in the normal sense and just checks that none of the three failure conditions above obtain
checkKinds :: ValT AbstractTy -> KindCheckM AbstractTy ()
checkKinds = \case
  Abstraction _ -> pure ()
  ThunkT (CompT _ (CompTBody nev)) -> traverse_ checkKinds nev
  BuiltinFlat{} -> pure ()
  Datatype tn args -> do
    DataDeclaration _ numVars _  <- lookupDeclaration tn
    let numArgsActual = V.length args
        numArgsExpected = review intCount numVars
    unless (numArgsActual == numArgsExpected) $ throwError (IncorrectNumArgs tn numVars args)
    traverse_ checkKinds args
 where
   checkCtor :: Constructor AbstractTy -> KindCheckM AbstractTy ()
   checkCtor (Constructor _ args) = traverse_ checkKinds args 
