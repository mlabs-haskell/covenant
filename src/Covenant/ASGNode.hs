module Covenant.ASGNode
  ( Id (..),
    typeId,
    Arg (..),
    Bound (..),
    Ref (..),
    typeRef,
    CompNode,
  )
where

import Control.Monad.Except (MonadError (throwError))
import Control.Monad.HashCons (MonadHashCons (lookupRef))
import Covenant.Constant (AConstant)
import Covenant.Ledger (LedgerAccessor, LedgerDestructor)
import Covenant.Prim (OneArgFunc, SixArgFunc, ThreeArgFunc, TwoArgFunc)
import Covenant.Type (CompT, ValT)
import Data.Kind (Type)
import Data.Word (Word64)

-- | @since 1.0.0
data TypeError
  = -- | The specified 'Id' doesn't refer to any 'ASGNode'. Under normal
    -- circumstances, this error cannot arise; it is only possible when 'Id's are
    -- being improperly reused outside of their enclosing 'MonadHashCons'
    -- computation.
    BrokenIdReference Id
  | -- | Attempt to return the specified computation type, instead of a value
    -- type.
    ReturnCompType CompT
  | -- | Attempt to force the specified computation type, instead of a thunk.
    ForceCompType CompT
  | -- | Attempt to force a non-thunk value type.
    ForceNonThunk ValT
  | -- | Attempt to apply an argument to a value type.
    ApplyToValueType ValT
  | -- | Attempt to use a computation type as an argument.
    CompTypeArgument CompT
  | -- | Lambda returns a value type.
    LambdaReturnValueType ValT
  | -- | Attempt to apply arguments to a return.
    ReturnApplyArgument ValT
  | -- Incompatible argument types in application: expected argument, then actual argument.
    IncompatibleArgumentTypes ValT ValT
  deriving stock (Eq, Show)

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

typeId ::
  forall (m :: Type -> Type).
  (MonadHashCons Id ASGNode m, MonadError TypeError m) =>
  Id -> m (Either CompT ValT)
typeId i =
  lookupRef i >>= \case
    Nothing -> throwError . BrokenIdReference $ i
    Just asgNode -> pure $ case asgNode of
      ACompNode t _ -> Left t
      AValNode t _ -> Right t

data Arg = Arg ValT Word64
  deriving stock (Eq, Ord, Show)

data Bound = Bound ValT Word64
  deriving stock (Eq, Ord, Show)

-- | A general reference in a Covenant program. This is one of the following:
--
-- * A computation, represented by its unique 'Id';
-- * A function argument, represented by an 'Arg'; or
-- * A @let@-bound variable, represented by a 'Bound'.
--
-- @since 1.0.0
data Ref = AnArg Arg | AnId Id | ABound Bound
  deriving stock
    ( -- | @since 1.0.0
      Eq,
      -- | @since 1.0.0
      Ord,
      -- | @since 1.0.0
      Show
    )

typeRef ::
  forall (m :: Type -> Type).
  (MonadHashCons Id ASGNode m, MonadError TypeError m) =>
  Ref -> m (Either CompT ValT)
typeRef = \case
  AnArg (Arg t _) -> pure . pure $ t
  AnId i -> typeId i
  ABound (Bound t _) -> pure . pure $ t

data CompNode
  = LamInternal ValT Id
  | ForceInternal Ref
  | ReturnInternal Ref
  | AppInternal Id Ref
  deriving stock (Eq, Ord, Show)

-- | A call to a Plutus primitive.
--
-- @since 1.0.0
data PrimCall
  = PrimCallOne OneArgFunc Ref
  | PrimCallTwo TwoArgFunc Ref Ref
  | PrimCallThree ThreeArgFunc Ref Ref Ref
  | PrimCallSix SixArgFunc Ref Ref Ref Ref Ref Ref
  deriving stock
    ( -- | @since 1.0.0
      Eq,
      -- | @since 1.0.0
      Ord,
      -- | @since 1.0.0
      Show
    )

data ValNode
  = LitInternal AConstant
  | ThunkInternal Id
  | ReceiveInternal Id
  | LetInternal Ref Ref
  | PrimAppInternal PrimCall
  | LedgerAccessInternal LedgerAccessor Ref
  | LedgerDestructInternal LedgerDestructor Id Ref
  deriving stock (Eq, Ord, Show)

data ASGNode = ACompNode CompT CompNode | AValNode ValT ValNode
  deriving stock (Eq, Ord, Show)
