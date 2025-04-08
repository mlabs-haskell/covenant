module Covenant.Internal.Term
  ( Id (..),
    Arg (..),
    Ref (..),
    CompNodeInfo (..),
    ValNodeInfo (..),
    ASGNode (..),
    ASGNodeType (..),
  )
where

import Covenant.Constant (AConstant)
import Covenant.Internal.Type (AbstractTy, CompT, ValT)
import Covenant.Prim (OneArgFunc, ThreeArgFunc, TwoArgFunc)
import Data.Vector (Vector)
import Data.Word (Word64)

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
