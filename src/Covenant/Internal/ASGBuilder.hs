{-# LANGUAGE TemplateHaskell #-}

module Covenant.Internal.ASGBuilder
  ( ASGBuilderState (..),
    ASGBuilder (..),
    ASGBuilderError (..),
    runASGBuilder,
    idOf,
    lit,
    prim,
    app,
  )
where

import Control.Monad.Except (ExceptT, liftEither, runExceptT)
import Control.Monad.State.Strict (State, gets, modify', runState)
import Covenant.Constant (AConstant)
import Covenant.Internal.ASGNode
  ( ASGNode (App, Lit, Prim),
    Id (Id),
    PrimCall,
    Ref,
  )
import Covenant.Internal.ASGType (ASGType, HasType (typeOf), TypeError, typeApp)
import Data.Bimap (Bimap)
import Data.Bimap qualified as Bimap
import Data.Kind (Type)
import Optics.Getter (view)
import Optics.Setter (over)
import Optics.TH (makeFieldLabelsNoPrefix)

newtype ASGBuilderState = ASGBuilderState {binds :: Bimap Id ASGNode}
  deriving (Eq, Ord) via Bimap Id ASGNode
  deriving stock (Show)

makeFieldLabelsNoPrefix ''ASGBuilderState

-- | A helper monad for building up Covenant programs. In particular, this
-- enables hash consing.
--
-- @since 1.0.0
newtype ASGBuilder (a :: Type) = ASGBuilder (ExceptT ASGBuilderError (State ASGBuilderState) a)
  deriving
    ( -- | @since 1.0.0
      Functor,
      -- | @since 1.0.0
      Applicative,
      -- | @since 1.0.0
      Monad
    )
    via (ExceptT ASGBuilderError (State ASGBuilderState))

-- | The errors that can occur during the construction of an ASG
--
-- @since 1.0.0
data ASGBuilderError
  = ATypeError TypeError

-- | Run a computation in the ASGBuilder monad
--
-- @since 1.0.0
runASGBuilder :: ASGBuilder a -> ASGBuilderState -> (Either ASGBuilderError a, ASGBuilderState)
runASGBuilder (ASGBuilder m) s =
  let stateM = runExceptT m
   in (runState stateM) s

-- | Construct a literal (constant) value.
--
-- @since 1.0.0
lit :: AConstant -> ASGBuilder Id
lit = idOf . Lit

-- | Construct a primitive function call.
--
-- @since 1.0.0
prim :: PrimCall -> ASGBuilder Id
prim = idOf . Prim

-- | Construct a function application. The first argument is (an expression
-- evaluating to) a function, the second argument is (an expression evaluating
-- to) an argument.
--
-- @since 1.0.0
app :: Ref -> Ref -> ASGBuilder Id
app fun arg =
  let tyFun = typeOf fun
      tyArg = typeOf arg
   in do
        tyRes <- liftEither . liftTypeError $ typeApp tyFun tyArg
        idOf tyRes (App fun arg)
  where
    liftTypeError :: Either TypeError a -> Either ASGBuilderError a
    liftTypeError (Left e) = Left $ ATypeError e
    liftTypeError (Right a) = Right a

-- Given a node, return its unique `Id`. If this is a node we've seen before in
-- the current `ExprBuilder` context, this `Id` will be looked up and reused;
-- otherwise, a fresh `Id` will be assigned, and the node cached to ensure we
-- have a reference to it henceforth.
idOf :: ASGType -> ASGNode -> ASGBuilder Id
idOf ty e = ASGBuilder $ do
  existingId <- gets (Bimap.lookupR e . view #binds)
  case existingId of
    Nothing -> do
      hasAnyBindings <- gets (Bimap.null . view #binds)
      newId <-
        if hasAnyBindings
          then (\(Id highest _) -> Id (highest + 1) ty) <$> gets (fst . Bimap.findMax . view #binds)
          else pure $ Id 0 ty
      newId <$ modify' (over #binds (Bimap.insert newId e))
    Just nodeId -> pure nodeId
