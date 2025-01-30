module Covenant.Internal.ASGNode
  ( Id (..),
    Arg (..),
    Bound (..),
    Ref (..),
    PrimCall (..),
    ASGNode (..),
  )
where

import Covenant.Constant (AConstant)
import Covenant.Prim (OneArgFunc, SixArgFunc, ThreeArgFunc, TwoArgFunc)
import Data.Word (Word64)

-- | A unique identifier for a node in a Covenant program.
--
-- @since 1.0.0
newtype Id = Id Word64
  deriving
    ( -- | @since 1.0.0
      Eq,
      -- | @since 1.0.0
      Ord
    )
    via Word64
  deriving stock
    ( -- | @since 1.0.0
      Show
    )

-- | An argument passed to a function in a Covenant program.
--
-- @since 1.0.0
newtype Arg = Arg Word64
  deriving
    ( -- | @since 1.0.0
      Eq,
      -- | @since 1.0.0
      Ord
    )
    via Word64
  deriving stock
    ( -- | @since 1.0.0
      Show
    )

-- | A @let@-bound variable in a Covenant program.
--
-- @since 1.0.0
newtype Bound = Bound Word64
  deriving
    ( -- | @since 1.0.0
      Eq,
      -- | @since 1.0.0
      Ord
    )
    via Word64
  deriving stock
    ( -- | @since 1.0.0
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
