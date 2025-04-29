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
import Covenant.Internal.Rename (RenameError)
import Covenant.Internal.Type (AbstractTy, CompT, ValT)
import Covenant.Internal.Unification (TypeAppError)
import Covenant.Prim (OneArgFunc, ThreeArgFunc, TwoArgFunc)
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
    -- @since 1.0.0
    LambdaResultsInValType (ValT AbstractTy)
  | -- | The body of a lambda results in a computation-typed node which isn't
    -- a return, which isn't allowed.
    --
    -- @since 1.0.0
    LambdaResultsInNonReturn (CompT AbstractTy)
  | -- | Can't return an error node, but we tried anyway.
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
  Id -> m ASGNodeType
typeId i = do
  lookedUp <- lookupRef i
  case lookedUp of
    Nothing -> throwError . BrokenIdReference $ i
    Just node -> pure . typeASGNode $ node

-- | An argument passed to a function in a Covenant program. We represent this
-- as a combination of scope (as a De Bruijn index) and an index (representing
-- the position of the argument), together with its type.
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

-- | A general reference in a Covenant program. This is one of the following:
--
-- * An ASG node, represented by its unique 'Id';
-- * A function argument, represented by an 'Arg'.
--
-- @since 1.0.0
data Ref = AnArg Arg | AnId Id
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
  Ref -> m ASGNodeType
typeRef = \case
  AnArg arg -> pure . ValNodeType . typeArg $ arg
  AnId i -> typeId i

-- | Computation-term-specific node information.
--
-- @since 1.0.0
data CompNodeInfo
  = -- | This node is a Plutus primop taking one argument.
    --
    -- @since 1.0.0
    Builtin1Internal OneArgFunc
  | -- | This node is a Plutus primop taking two arguments.
    --
    -- @since 1.0.0
    Builtin2Internal TwoArgFunc
  | -- | This node is a Plutus primop taking three arguments.
    --
    -- @since 1.0.0
    Builtin3Internal ThreeArgFunc
  | -- | This node is a lambda, with a link to its body.
    --
    -- @since 1.0.0
    LamInternal Id
  | -- | This node is forcing a thunk, as indicated by the 'Ref'.
    --
    -- @since 1.0.0
    ForceInternal Ref
  | -- | This node is returning a value-typed term, as indicated by the 'Ref'.
    --
    -- @since 1.0.0
    ReturnInternal Ref
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
  = -- | This node is a compile-time literal of a flat builtin type.
    --
    -- @since 1.0.0
    LitInternal AConstant
  | -- | This node is an application, with the computation indicated by
    -- the 'Id' field, and the arguments being applied in order by the 'Vector'
    -- field.
    --
    -- @since 1.0.0
    AppInternal Id (Vector Ref)
  | -- | This node is a thunk of a computation indicated by the 'Id'.
    --
    -- @since 1.0.0
    ThunkInternal Id
  deriving stock
    ( -- | @since 1.0.0
      Eq,
      -- | @since 1.0.0
      Ord,
      -- | @since 1.0.0
      Show
    )

-- | A single node in a Covenant ASG. These are either value-typed,
-- computation-typed or error nodes; the first two of these also carry their
-- types.
--
-- @since 1.0.0
data ASGNode
  = ACompNode (CompT AbstractTy) CompNodeInfo
  | AValNode (ValT AbstractTy) ValNodeInfo
  | AnError
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
