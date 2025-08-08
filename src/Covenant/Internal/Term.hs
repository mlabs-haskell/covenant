module Covenant.Internal.Term
  ( CovenantTypeError (..),
    Id (..),
    typeId,
    Arg (..),
    typeArg,
    Ref (..),
    typeRef,
    CompNodeInfo (..),
    ValNodeInfo (..),
    ASGNode (..),
    typeASGNode,
    ASGNodeType (..),
  )
where

import Control.Monad.Except (MonadError (throwError))
import Control.Monad.HashCons (MonadHashCons (lookupRef))
import Covenant.Constant (AConstant)
import Covenant.DeBruijn (DeBruijn)
import Covenant.Index (Index)
import Covenant.Internal.KindCheck (EncodingArgErr)
import Covenant.Internal.Rename (RenameError, UnRenameError)
import Covenant.Internal.Type
  ( AbstractTy,
    BuiltinFlatT,
    CompT,
    ValT,
  )
import Covenant.Internal.Unification (TypeAppError)
import Covenant.Prim (OneArgFunc, SixArgFunc, ThreeArgFunc, TwoArgFunc)
import Data.Kind (Type)
import Data.Vector (Vector)
import Data.Word (Word64)

-- | An error that can arise during the construction of an ASG by programmatic
-- means.
--
-- @since 1.0.0
data CovenantTypeError
  = -- | An 'Id' has no corresponding node. This error should not arise under
    -- normal circumstances: the most likely explanation is that you're using an
    -- 'Id' that was made by a different ASG builder computation.
    --
    -- @since 1.0.0
    BrokenIdReference Id
  | -- | Computation-typed nodes can't be forced, but we tried anyway.
    --
    -- @since 1.0.0
    ForceCompType (CompT AbstractTy)
  | -- | Value-typed nodes that aren't thunks can't be forced, but we tried anyway.
    --
    -- @since 1.0.0
    ForceNonThunk (ValT AbstractTy)
  | -- | Error nodes can't be forced, but we tried anyway.
    --
    -- @since 1.0.0
    ForceError
  | -- | Value-typed nodes can't be thunked, but we tried anyway.
    --
    -- @since 1.0.0
    ThunkValType (ValT AbstractTy)
  | -- | Error nodes can't be thunked, but we tried anyway.
    --
    -- @since 1.0.0
    ThunkError
  | -- | Arguments can't be applied to a value-typed node, but we tried anyway.
    --
    -- @since 1.0.0
    ApplyToValType (ValT AbstractTy)
  | -- | Arguments can't be applied to error nodes, but we tried anyway.
    --
    -- @since 1.0.0
    ApplyToError
  | -- | Computation-typed nodes can't be applied as arguments, but we tried anyway.
    --
    -- @since 1.0.0
    ApplyCompType (CompT AbstractTy)
  | -- | Renaming the function in an application failed.
    --
    -- @since 1.0.0
    RenameFunctionFailed (CompT AbstractTy) RenameError
  | -- | Renaming an argument in an application failed.
    --
    -- @since 1.0.0
    RenameArgumentFailed (ValT AbstractTy) RenameError
  | -- | We failed to unify an expected argument type with the type of the
    -- argument we were actually given.
    --
    -- @since 1.0.0
    UnificationError TypeAppError
  | -- | An argument was requested that doesn't exist.
    --
    -- @since 1.0.0
    NoSuchArgument DeBruijn (Index "arg")
  | -- | Can't return a computation-typed node, but we tried anyway.
    --
    -- @since 1.0.0
    ReturnCompType (CompT AbstractTy)
  | -- | The body of a lambda results in a value-typed node, which isn't allowed.
    --
    -- @since 1.2.0
    LambdaResultsInCompType (CompT AbstractTy)
  | -- | The body of a lambda results in a computation-typed node which isn't
    -- a return, which isn't allowed.
    --
    -- @since 1.0.0
    LambdaResultsInNonReturn (CompT AbstractTy)
  | -- | A lambda body's return is wrapping an error, instead of being directly
    -- an error. This should not happen under normal circumstances and is most
    -- certainly a bug.
    --
    -- @since 1.0.0
    ReturnWrapsError
  | -- | We tried to return a computation-typed node, but this isn't allowed.
    --
    -- @since 1.0.0
    ReturnWrapsCompType (CompT AbstractTy)
  | -- | The result of an application is not what the computation being
    -- applied expected.
    --
    -- First field is the expected type, the second is what we actually got.
    --
    -- @since 1.0.0
    WrongReturnType (ValT AbstractTy) (ValT AbstractTy)
  | -- @since 1.1.0

    -- | Wraps an encoding argument mismatch error from KindCheck
    EncodingError (EncodingArgErr AbstractTy)
  | -- | The first argument to a catamorphism wasn't an algebra.
    --
    -- @since 1.1.0
    CataNotAnAlgebra ASGNodeType
  | -- | The second argument to a catamorphism wasn't a value type.
    --
    -- @since 1.1.0
    CataApplyToNonValT ASGNodeType
  | -- | The second argument to a catamorphism is a builtin type, but not one
    -- we can eliminate with a catamorphism.
    --
    -- @since 1.1.0
    CataWrongBuiltinType BuiltinFlatT
  | -- | The second argument to a catamorphism is a value type, but not one we
    -- can eliminate with a catamorphism. Usually, this means it's a variable.
    --
    -- @since 1.1.0
    CataWrongValT (ValT AbstractTy)
  | -- | The provided algebra is not suitable for the given type.
    --
    -- @since 1.1.0
    CataUnsuitable (CompT AbstractTy) (ValT AbstractTy)
  | -- | Someone attempted to construct a tyvar using a DB index or argument position
    --   which refers to a scope (or argument) that does not exist.3
    -- @since 1.2.0
    OutOfScopeTyVar DeBruijn (Index "tyvar")
  | -- | We failed to rename an "instantiation type" supplied to `app`
    -- @since 1.2.0
    FailedToRenameInstantiation RenameError
  | -- | With recent changes, undoRename is no longer deterministic, and we might get an error, which we have to "lift"
    -- @since 1.2.0
    UndoRenameFailure UnRenameError
  deriving stock
    ( -- | @since 1.0.0
      Eq,
      -- | @since 1.0.0
      Show
    )

-- | A unique identifier for a node in a Covenant program.
--
-- @since 1.0.0
newtype Id = Id Word64
  deriving
    ( -- | @since 1.0.0
      Eq,
      -- | @since 1.0.0
      Ord,
      -- | @since 1.0.0
      Bounded,
      -- | Needed for internal reasons, even though this type class is terrible.
      --
      -- @since 1.0.0
      Enum
    )
    via Word64
  deriving stock
    ( -- | @since 1.0.0
      Show
    )

-- Get the type of an `Id`, or fail.
typeId ::
  forall (m :: Type -> Type).
  (MonadHashCons Id ASGNode m, MonadError CovenantTypeError m) =>
  Id ->
  m ASGNodeType
typeId i = do
  lookedUp <- lookupRef i
  case lookedUp of
    Nothing -> throwError . BrokenIdReference $ i
    Just node -> pure . typeASGNode $ node

-- | An argument passed to a function in a Covenant program.
--
-- @since 1.0.0
data Arg = Arg DeBruijn (Index "arg") (ValT AbstractTy)
  deriving stock
    ( -- | @since 1.0.0
      Eq,
      -- | @since 1.0.0
      Ord,
      -- | @since 1.0.0
      Show
    )

-- Helper to get the type of an argument.
typeArg :: Arg -> ValT AbstractTy
typeArg (Arg _ _ t) = t

-- | A general reference in a Covenant program.
--
-- @since 1.0.0
data Ref
  = -- | A function argument.
    --
    -- @since 1.0.0
    AnArg Arg
  | -- | A link to an ASG node.
    --
    -- @since 1.0.0
    AnId Id
  deriving stock
    ( -- | @since 1.0.0
      Eq,
      -- | @since 1.0.0
      Ord,
      -- | @since 1.0.0
      Show
    )

-- Helper for getting a type for any reference.
typeRef ::
  forall (m :: Type -> Type).
  (MonadHashCons Id ASGNode m, MonadError CovenantTypeError m) =>
  Ref ->
  m ASGNodeType
typeRef = \case
  AnArg arg -> pure . ValNodeType . typeArg $ arg
  AnId i -> typeId i

-- | Computation-term-specific node information.
--
-- @since 1.0.0
data CompNodeInfo
  = Builtin1Internal OneArgFunc
  | Builtin2Internal TwoArgFunc
  | Builtin3Internal ThreeArgFunc
  | Builtin6Internal SixArgFunc
  | LamInternal Ref
  | ForceInternal Ref
  deriving stock
    ( -- | @since 1.0.0
      Eq,
      -- | @since 1.0.0
      Ord,
      -- | @since 1.0.0
      Show
    )

-- | Value-term-specific node information.
--
-- @since 1.0.0
data ValNodeInfo
  = LitInternal AConstant
  | AppInternal Id (Vector Ref)
  | ThunkInternal Id
  | -- | @since 1.1.0
    CataInternal Ref Ref
  deriving stock
    ( -- | @since 1.0.0
      Eq,
      -- | @since 1.0.0
      Ord,
      -- | @since 1.0.0
      Show
    )

-- | A single node in a Covenant ASG. Where appropriate, these carry their
-- types.
--
-- @since 1.0.0
data ASGNode
  = -- | A computation-typed node.
    --
    -- @since 1.0.0
    ACompNode (CompT AbstractTy) CompNodeInfo
  | -- | A value-typed node
    --
    -- @since 1.0.0
    AValNode (ValT AbstractTy) ValNodeInfo
  | -- | An error node.
    --
    -- @since 1.0.0
    AnError
  deriving stock
    ( -- | @since 1.0.0
      Eq,
      -- | @since 1.0.0
      Ord,
      -- | @since 1.0.0
      Show
    )

-- | Produces the type of any ASG node.
--
-- @since 1.0.0
typeASGNode :: ASGNode -> ASGNodeType
typeASGNode = \case
  ACompNode t _ -> CompNodeType t
  AValNode t _ -> ValNodeType t
  AnError -> ErrorNodeType

-- | Helper data type representing the type of any ASG node whatsoever.
--
-- @since 1.0.0
data ASGNodeType
  = CompNodeType (CompT AbstractTy)
  | ValNodeType (ValT AbstractTy)
  | ErrorNodeType
  deriving stock
    ( -- | @since 1.0.0
      Eq,
      -- | @since 1.0.0
      Ord,
      -- | @since 1.0.0
      Show
    )
