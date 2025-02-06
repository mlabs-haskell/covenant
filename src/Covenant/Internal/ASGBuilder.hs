{-# LANGUAGE TemplateHaskell #-}

module Covenant.Internal.ASGBuilder
  ( -- * Data Types
    ASGBuilderState (..),
    ASGBuilder (..),
    ASGBuilderError (..),
    TypeError (..),

    -- * Functions
    runASGBuilder,
    idOf,
    lit,
    prim,
    app,
  )
where

import Control.Monad.Except (ExceptT, liftEither, runExceptT)
import Control.Monad.State.Strict (State, gets, modify', runState)
import Covenant.Constant (AConstant, TyConstant)
import Covenant.Internal.ASGNode
  ( ASGNode (App, Lit, Prim),
    ASGType (TyConstant, TyLam),
    Id (Id),
    PrimCall (PrimCallOne, PrimCallSix, PrimCallThree, PrimCallTwo),
    Ref,
    typeOfRef,
  )
import Covenant.Prim (OneArgFunc, SixArgFunc, ThreeArgFunc, TwoArgFunc, typeOfOneArgFunc, typeOfSixArgFunc, typeOfThreeArgFunc, typeOfTwoArgFunc)
import Data.Bimap (Bimap)
import Data.Bimap qualified as Bimap
import Data.Kind (Type)
import Data.Vector (Vector)
import Data.Vector qualified as Vector
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

-- | The errors that come up while resolving types.
--
-- @since 1.0.0
data TypeError
  = TyErrAppNotALambda ASGType
  | TyErrAppArgMismatch ASGType ASGType -- expected, received
  | TyErrPrimNotAConstant ASGType
  | TyErrPrimArgMismatch (Vector TyConstant) (Vector TyConstant) -- exptected, received

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
prim p = do
  tyRes <- liftEither . liftTypeError $ typePrim p
  idOf tyRes (Prim p)

-- | Construct a function application. The first argument is (an expression
-- evaluating to) a function, the second argument is (an expression evaluating
-- to) an argument.
--
-- @since 1.0.0
app :: Ref -> Ref -> ASGBuilder Id
app fun arg =
  let tyFun = typeOfRef fun
      tyArg = typeOfRef arg
   in do
        tyRes <- liftEither . liftTypeError $ typeApp tyFun tyArg
        idOf tyRes (App fun arg)

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

-- Typing Helpers

liftTypeError :: Either TypeError a -> Either ASGBuilderError a
liftTypeError (Left e) = Left $ ATypeError e
liftTypeError (Right a) = Right a

typeApp :: ASGType -> ASGType -> Either TypeError ASGType
typeApp tyFun tyArg = case tyFun of
  TyLam tyParam tyRes ->
    if tyParam == tyArg
      then Right tyRes
      else Left $ TyErrAppArgMismatch tyParam tyArg
  _ -> Left $ TyErrAppNotALambda tyFun

typePrim :: PrimCall -> Either TypeError ASGType
typePrim = fmap TyConstant . go
  where
    go :: PrimCall -> Either TypeError TyConstant
    go (PrimCallOne fun arg1) = do
      tyArg1 <- getConstantOrThrow $ typeOfRef arg1
      typeOneArgFunc fun tyArg1
    go (PrimCallTwo fun arg1 arg2) = do
      tyArg1 <- getConstantOrThrow $ typeOfRef arg1
      tyArg2 <- getConstantOrThrow $ typeOfRef arg2
      typeTwoArgFunc fun tyArg1 tyArg2
    go (PrimCallThree fun arg1 arg2 arg3) = do
      tyArg1 <- getConstantOrThrow $ typeOfRef arg1
      tyArg2 <- getConstantOrThrow $ typeOfRef arg2
      tyArg3 <- getConstantOrThrow $ typeOfRef arg3
      typeThreeArgFunc fun tyArg1 tyArg2 tyArg3
    go (PrimCallSix fun arg1 arg2 arg3 arg4 arg5 arg6) = do
      tyArg1 <- getConstantOrThrow $ typeOfRef arg1
      tyArg2 <- getConstantOrThrow $ typeOfRef arg2
      tyArg3 <- getConstantOrThrow $ typeOfRef arg3
      tyArg4 <- getConstantOrThrow $ typeOfRef arg4
      tyArg5 <- getConstantOrThrow $ typeOfRef arg5
      tyArg6 <- getConstantOrThrow $ typeOfRef arg6
      typeSixArgFunc fun tyArg1 tyArg2 tyArg3 tyArg4 tyArg5 tyArg6

    getConstantOrThrow :: ASGType -> Either TypeError TyConstant
    getConstantOrThrow (TyConstant c) = Right c
    getConstantOrThrow ty = Left $ TyErrPrimNotAConstant ty

typeOneArgFunc :: OneArgFunc -> TyConstant -> Either TypeError TyConstant
typeOneArgFunc fun tyArg1 =
  let (tyParam1, tyRes) = typeOfOneArgFunc fun
   in if tyParam1 == tyArg1
        then Right tyRes
        else Left $ TyErrPrimArgMismatch (Vector.fromList [tyParam1]) (Vector.fromList [tyArg1])

typeTwoArgFunc :: TwoArgFunc -> TyConstant -> TyConstant -> Either TypeError TyConstant
typeTwoArgFunc fun tyArg1 tyArg2 =
  let (tyParam1, tyParam2, tyRes) = typeOfTwoArgFunc fun
   in if (tyParam1, tyParam2) == (tyArg1, tyArg2)
        then Right tyRes
        else Left $ TyErrPrimArgMismatch (Vector.fromList [tyParam1, tyParam2]) (Vector.fromList [tyArg1, tyArg2])

typeThreeArgFunc :: ThreeArgFunc -> TyConstant -> TyConstant -> TyConstant -> Either TypeError TyConstant
typeThreeArgFunc fun tyArg1 tyArg2 tyArg3 =
  let (tyParam1, tyParam2, tyParam3, tyRes) = typeOfThreeArgFunc fun
   in if (tyParam1, tyParam2, tyParam3) == (tyArg1, tyArg2, tyArg3)
        then Right tyRes
        else Left $ TyErrPrimArgMismatch (Vector.fromList [tyParam1, tyParam2, tyParam3]) (Vector.fromList [tyArg1, tyArg2, tyArg3])

typeSixArgFunc :: SixArgFunc -> TyConstant -> TyConstant -> TyConstant -> TyConstant -> TyConstant -> TyConstant -> Either TypeError TyConstant
typeSixArgFunc fun tyArg1 tyArg2 tyArg3 tyArg4 tyArg5 tyArg6 =
  let (tyParam1, tyParam2, tyParam3, tyParam4, tyParam5, tyParam6, tyRes) = typeOfSixArgFunc fun
   in if (tyParam1, tyParam2, tyParam3, tyParam4, tyParam5, tyParam6) == (tyArg1, tyArg2, tyArg3, tyArg4, tyArg5, tyArg6)
        then Right tyRes
        else
          Left $
            TyErrPrimArgMismatch
              (Vector.fromList [tyParam1, tyParam2, tyParam3, tyParam4, tyParam5, tyParam6])
              (Vector.fromList [tyArg1, tyArg2, tyArg3, tyArg4, tyArg5, tyArg6])