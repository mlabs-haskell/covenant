module Covenant.Internal.Term
  ( Id (..),
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
import Covenant.Internal.Type (AbstractTy, CompT, ValT)
import Covenant.Prim (OneArgFunc, ThreeArgFunc, TwoArgFunc)
import Data.Kind (Type)
import Data.Vector (Vector)
import Data.Word (Word64)

-- | @since 1.0.0
newtype CovenantTypeError = BrokenIdReference Id

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

-- | @since 1.0.0
typeId ::
  forall (m :: Type -> Type).
  (MonadHashCons Id ASGNode m, MonadError CovenantTypeError m) =>
  Id -> m ASGNodeType
typeId i = do
  lookedUp <- lookupRef i
  case lookedUp of
    Nothing -> throwError . BrokenIdReference $ i
    Just node -> pure . typeASGNode $ node

-- | An argument passed to a function in a Covenant program.
--
-- @since 1.0.0
data Arg = Arg Word64 (ValT AbstractTy)
  deriving stock
    ( -- | @since 1.0.0
      Eq,
      -- | @since 1.0.0
      Ord,
      -- | @since 1.0.0
      Show
    )

-- | @since 1.0.0
typeArg :: Arg -> ValT AbstractTy
typeArg (Arg _ t) = t

-- | A general reference in a Covenant program. This is one of the following:
--
-- * A computation, represented by its unique 'Id';
-- * A function argument, represented by an 'Arg'; or
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

-- | @since 1.0.0
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
  = Builtin1Internal OneArgFunc
  | Builtin2Internal TwoArgFunc
  | Builtin3Internal ThreeArgFunc
  | LamInternal Id
  | ForceInternal Ref
  | ReturnInternal Ref
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
  deriving stock
    ( -- | @since 1.0.0
      Eq,
      -- | @since 1.0.0
      Ord,
      -- | @since 1.0.0
      Show
    )

-- | A single node in a Covenant ASG.
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

-- | @since 1.0.0
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
