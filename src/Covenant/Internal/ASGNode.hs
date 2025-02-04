{-# LANGUAGE PatternSynonyms #-}

module Covenant.Internal.ASGNode
  ( Id (..),
    Arg (..),
    Bound (..),
    Ref (..),
    PrimCall (..),
    ASGNode (..),
    pattern Lit,
    pattern Prim,
    pattern Lam,
    pattern Let,
    pattern App,
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
      Ord,
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

-- Used only by the ASGBuilder
data ASGNode
  = LitInternal AConstant
  | PrimInternal PrimCall
  | LamInternal Ref
  | LetInternal Ref Ref
  | AppInternal Ref Ref
  deriving stock
    ( -- | @since 1.0.0
      Eq,
      -- | @since 1.0.0
      Ord,
      -- | @since 1.0.0
      Show
    )

-- | @since 1.0.0
pattern Lit :: AConstant -> ASGNode
pattern Lit c <- LitInternal c

-- | @since 1.0.0
pattern Prim :: PrimCall -> ASGNode
pattern Prim p <- PrimInternal p

-- | @since 1.0.0
pattern Lam :: Ref -> ASGNode
pattern Lam r <- LamInternal r

-- | @since 1.0.0
pattern Let :: Ref -> Ref -> ASGNode
pattern Let rBind rBody <- LetInternal rBind rBody

-- | @since 1.0.0
pattern App :: Ref -> Ref -> ASGNode
pattern App rFun rArg <- AppInternal rFun rArg

{-# COMPLETE Lit, Prim, Lam, Let, App #-}
