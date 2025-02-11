module Covenant.Internal.ASGNode
  ( -- * Data Types
    Id (..),
    Arg (..),
    Bound (..),
    Ref (..),
    PrimCall (..),
    ASGNode (..),
    ASGType (..),

    -- * Functions
    typeOfRef,
  )
where

import Covenant.Constant (AConstant, TyExpr)
import Covenant.Prim (OneArgFunc, SixArgFunc, ThreeArgFunc, TwoArgFunc)
import Data.Word (Word64)

-- | A unique identifier for a node in a Covenant program.
--
-- @since 1.0.0
data Id = Id Word64 ASGType
  deriving stock
    ( -- | @since 1.0.0
      Eq,
      -- | @since 1.0.0
      Ord,
      -- | @since 1.0.0
      Show
    )

-- | An argument passed to a function in a Covenant program.
--
-- @since 1.0.0
data Arg = Arg Word64 ASGType
  deriving stock
    ( -- | @since 1.0.0
      Eq,
      -- | @since 1.0.0
      Ord,
      -- | @since 1.0.0
      Show
    )

-- | A @let@-bound variable in a Covenant program.
--
-- @since 1.0.0
data Bound = Bound Word64 ASGType
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

-- | A node in a Covenant program. Since Covenant programs are hash consed, they
-- form a graph, hence \'ASG\' - \'abstract syntax graph\'.
--
-- @since 1.0.0
data ASGNode
  = Lit AConstant
  | Prim PrimCall
  | Lam Ref
  | Let Ref Ref
  | App Ref Ref
  deriving stock
    ( -- | @since 1.0.0
      Eq,
      -- | @since 1.0.0
      Ord,
      -- | @since 1.0.0
      Show
    )

-- | The type of an @ASGNode@.
--
-- @since 1.0.0
data ASGType
  = TyExpr TyExpr
  | TyLam ASGType ASGType -- TyLam ArgType ResType
  deriving stock
    ( -- | @since 1.0.0
      Eq,
      -- | @since 1.0.0
      Ord,
      -- | @since 1.0.0
      Show
    )

--

typeOfRef :: Ref -> ASGType
typeOfRef = \case
  AnId (Id _ ty) -> ty
  AnArg (Arg _ ty) -> ty
  ABound (Bound _ ty) -> ty
