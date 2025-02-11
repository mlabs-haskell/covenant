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

import Control.Monad (unless)
import Control.Monad.Except (ExceptT, MonadError, liftEither, runExceptT)
import Control.Monad.State.Strict (State, gets, modify', runState)
import Covenant.Constant
  ( AConstant
      ( ABoolean,
        AByteString,
        AData,
        AList,
        APair,
        AString,
        AUnit,
        AnInteger
      ),
    TyExpr
      ( TyBoolean,
        TyByteString,
        TyInteger,
        TyList,
        TyPair,
        TyPlutusData,
        TyString,
        TyUnit
      ),
  )
import Covenant.Internal.ASGNode
  ( ASGNode (App, Lit, Prim),
    ASGType (TyExpr, TyLam),
    Id (Id),
    PrimCall (PrimCallOne, PrimCallSix, PrimCallThree, PrimCallTwo),
    Ref,
    typeOfRef,
  )
import Covenant.Prim (OneArgFunc, SixArgFunc, ThreeArgFunc, TwoArgFunc, typeOfOneArgFunc, typeOfSixArgFunc, typeOfThreeArgFunc, typeOfTwoArgFunc)
import Data.Bimap (Bimap)
import Data.Bimap qualified as Bimap
import Data.Foldable (traverse_)
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
      Monad,
      -- | @since 1.0.0
      MonadError ASGBuilderError
    )
    via (ExceptT ASGBuilderError (State ASGBuilderState))

-- | The errors that can occur during the construction of an ASG
--
-- @since 1.0.0
newtype ASGBuilderError = ATypeError TypeError
  deriving
    ( -- | @since 1.0.0
      Eq,
      -- | @since 1.0.0
      Show
    )
    via TypeError

-- | The errors that come up while resolving types.
--
-- @since 1.0.0
data TypeError
  = -- | Tried to apply a value @f@ to @x@, but @f@ was not a lambda.
    TyErrAppNotALambda
      -- | Type of @f@.
      ASGType
  | -- | Tried to apply a value @f@ to @x@, but @x@ was not of the expected type.
    TyErrAppArgMismatch
      -- | Expected type
      ASGType
      -- | Type of @x@
      ASGType
  | -- | Tried to call primitive function with an argument that is not a Plutus expression
    TyErrPrimArgNotAnExpr
      -- | Type of the given argument
      ASGType
  | -- | Tried to call a primitive function with incorrect arguments
    TyErrPrimArgMismatch
      -- | Types of expected arguments
      (Vector TyExpr)
      -- | Types of provided arguments
      (Vector TyExpr)
  | -- | Tried to construct where the items have different types.
    TyErrNonHomogenousList
  deriving stock
    ( -- | @since 1.0.0
      Eq,
      -- | @since 1.0.0
      Show
    )

-- | Run a computation in the ASGBuilder monad
--
-- @since 1.0.0
runASGBuilder :: ASGBuilder a -> ASGBuilderState -> (Either ASGBuilderError a, ASGBuilderState)
runASGBuilder (ASGBuilder m) s =
  let stateM = runExceptT m
   in runState stateM s

-- | Construct a literal (constant) value.
--
-- @since 1.0.0
lit :: AConstant -> ASGBuilder Id
lit c = do
  ty <- TyExpr <$> liftEither (typeLit c)
  idOf ty (Lit c)

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

typeLit :: AConstant -> Either ASGBuilderError TyExpr
typeLit = \case
  AUnit -> Right TyUnit
  ABoolean _ -> Right TyBoolean
  AnInteger _ -> Right TyInteger
  AByteString _ -> Right TyByteString
  AString _ -> Right TyString
  APair a b -> do
    tyA <- typeLit a
    tyB <- typeLit b
    pure $ TyPair tyA tyB
  AList ty elems -> do
    traverse_
      ( \v1 -> do
          ty' <- typeLit v1
          unless (ty' == ty) (Left $ ATypeError TyErrNonHomogenousList)
      )
      elems
    pure $ TyList ty
  AData _ -> pure TyPlutusData

typeApp :: ASGType -> ASGType -> Either TypeError ASGType
typeApp tyFun tyArg = case tyFun of
  TyLam tyParam tyRes ->
    if tyParam == tyArg
      then Right tyRes
      else Left $ TyErrAppArgMismatch tyParam tyArg
  _ -> Left $ TyErrAppNotALambda tyFun

typePrim :: PrimCall -> Either TypeError ASGType
typePrim = fmap TyExpr . go
  where
    go :: PrimCall -> Either TypeError TyExpr
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

    getConstantOrThrow :: ASGType -> Either TypeError TyExpr
    getConstantOrThrow (TyExpr c) = Right c
    getConstantOrThrow ty = Left $ TyErrPrimArgNotAnExpr ty

typeOneArgFunc :: OneArgFunc -> TyExpr -> Either TypeError TyExpr
typeOneArgFunc fun tyArg1 =
  let (tyParam1, tyRes) = typeOfOneArgFunc fun
   in if tyParam1 == tyArg1
        then Right tyRes
        else Left $ TyErrPrimArgMismatch (Vector.fromList [tyParam1]) (Vector.fromList [tyArg1])

typeTwoArgFunc :: TwoArgFunc -> TyExpr -> TyExpr -> Either TypeError TyExpr
typeTwoArgFunc fun tyArg1 tyArg2 =
  let (tyParam1, tyParam2, tyRes) = typeOfTwoArgFunc fun
   in if (tyParam1, tyParam2) == (tyArg1, tyArg2)
        then Right tyRes
        else Left $ TyErrPrimArgMismatch (Vector.fromList [tyParam1, tyParam2]) (Vector.fromList [tyArg1, tyArg2])

typeThreeArgFunc :: ThreeArgFunc -> TyExpr -> TyExpr -> TyExpr -> Either TypeError TyExpr
typeThreeArgFunc fun tyArg1 tyArg2 tyArg3 =
  let (tyParam1, tyParam2, tyParam3, tyRes) = typeOfThreeArgFunc fun
   in if (tyParam1, tyParam2, tyParam3) == (tyArg1, tyArg2, tyArg3)
        then Right tyRes
        else Left $ TyErrPrimArgMismatch (Vector.fromList [tyParam1, tyParam2, tyParam3]) (Vector.fromList [tyArg1, tyArg2, tyArg3])

typeSixArgFunc :: SixArgFunc -> TyExpr -> TyExpr -> TyExpr -> TyExpr -> TyExpr -> TyExpr -> Either TypeError TyExpr
typeSixArgFunc fun tyArg1 tyArg2 tyArg3 tyArg4 tyArg5 tyArg6 =
  let (tyParam1, tyParam2, tyParam3, tyParam4, tyParam5, tyParam6, tyRes) = typeOfSixArgFunc fun
   in if (tyParam1, tyParam2, tyParam3, tyParam4, tyParam5, tyParam6) == (tyArg1, tyArg2, tyArg3, tyArg4, tyArg5, tyArg6)
        then Right tyRes
        else
          Left $
            TyErrPrimArgMismatch
              (Vector.fromList [tyParam1, tyParam2, tyParam3, tyParam4, tyParam5, tyParam6])
              (Vector.fromList [tyArg1, tyArg2, tyArg3, tyArg4, tyArg5, tyArg6])
