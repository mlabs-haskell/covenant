{-# LANGUAGE PatternSynonyms #-}

module Covenant.Internal.ASGNode
  ( Id (..),
    Arg (..),
    Bound (..),
    Ref (..),
    PrimCall (..),
    ASGNode (..),
    TyASGNode (..),
    TyLam (..),
    pattern Lit,
    pattern Prim,
    pattern Lam,
    pattern Let,
    pattern App,
    pattern LedgerAccess,
    pattern LedgerDestruct,
    childIds,
    typeOfRef,
    typeOfNode,
  )
where

import Control.Monad.HashCons (MonadHashCons, lookupRef)
import Covenant.Constant (AConstant)
import Covenant.Internal.TyExpr (TyExpr)
import Covenant.Ledger (LedgerAccessor, LedgerDestructor)
import Covenant.Prim (OneArgFunc, ThreeArgFunc, TwoArgFunc)
import Data.Kind (Type)
import Data.Maybe (fromJust, mapMaybe)
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
data Arg = Arg Word64 TyASGNode
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
data Bound = Bound Word64 TyASGNode
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
  --   | PrimCallSix SixArgFunc Ref Ref Ref Ref Ref Ref
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
-- = Note
--
-- We use pattern synonyms to allow pattern-matching syntax to view 'ASGNode'
-- contents, but /not/ construct them. For this, you need to use the API
-- provided by 'Covenant.Internal.ASGBuilder.ASGBuilder'.
--
-- @since 1.0.0
data ASGNode
  = LitInternal TyExpr AConstant
  | PrimInternal TyASGNode PrimCall
  | LamInternal TyLam Ref
  | LetInternal TyASGNode Ref Ref
  | AppInternal TyASGNode Ref Ref
  | LedgerAccessInternal LedgerAccessor Ref
  | LedgerDestructInternal LedgerDestructor Ref Ref
  deriving stock
    ( -- | @since 1.0.0
      Eq,
      -- | @since 1.0.0
      Ord,
      -- | @since 1.0.0
      Show
    )

-- | A constant value.
--
-- @since 1.0.0
pattern Lit :: TyExpr -> AConstant -> ASGNode
pattern Lit ty c <- LitInternal ty c

-- | A call to a Plutus builtin.
--
-- @since 1.0.0
pattern Prim :: TyASGNode -> PrimCall -> ASGNode
pattern Prim ty p <- PrimInternal ty p

-- | A lambda abstraction: the node contents are its body.
--
-- @since 1.0.0
pattern Lam :: TyLam -> Ref -> ASGNode
pattern Lam ty r <- LamInternal ty r

-- | A `let` binding. The first 'Ref' is the binding, while the second is the
-- body the binding is used in.
--
-- @since 1.0.0
pattern Let :: TyASGNode -> Ref -> Ref -> ASGNode
pattern Let ty rBind rBody <- LetInternal ty rBind rBody

-- | A function application. The first 'Ref' is the function expression, while
-- the second is the argument to be applied.
--
-- @since 1.0.0
pattern App :: TyASGNode -> Ref -> Ref -> ASGNode
pattern App ty rFun rArg <- AppInternal ty rFun rArg

-- | An accessor for a ledger type.
--
-- @since 1.0.0
pattern LedgerAccess :: LedgerAccessor -> Ref -> ASGNode
pattern LedgerAccess acc rArg <- LedgerAccessInternal acc rArg

-- | A destructor for a ledger sum. The first 'Ref' is for a destructor
-- function, while the second is the argument to be destructured.
--
-- @since 1.0.0
pattern LedgerDestruct :: LedgerDestructor -> Ref -> Ref -> ASGNode
pattern LedgerDestruct d rDest rArg <- LedgerDestructInternal d rDest rArg

{-# COMPLETE Lit, Prim, Lam, Let, App, LedgerAccess, LedgerDestruct #-}

-- | The type of an @ASGNode@.
--
-- @since 1.0.0
data TyASGNode
  = ATyExpr TyExpr
  | ATyLam TyLam
  deriving stock
    ( -- | @since 1.0.0
      Eq,
      -- | @since 1.0.0
      Ord,
      -- | @since 1.0.0
      Show
    )

-- | The type of a @Lam@.
--
-- @since 1.0.0
data TyLam
  = TyLam
      -- | argument type
      TyASGNode
      -- | return type
      TyASGNode
  deriving stock
    ( -- | @since 1.0.0
      Eq,
      -- | @since 1.0.0
      Ord,
      -- | @since 1.0.0
      Show
    )

-- | @since 1.0.0
childIds :: ASGNode -> [Id]
childIds = \case
  LitInternal _ _ -> []
  PrimInternal _ p -> case p of
    PrimCallOne _ r1 -> mapMaybe refToId [r1]
    PrimCallTwo _ r1 r2 -> mapMaybe refToId [r1, r2]
    PrimCallThree _ r1 r2 r3 -> mapMaybe refToId [r1, r2, r3]
  -- PrimCallSix _ r1 r2 r3 r4 r5 r6 -> mapMaybe refToId [r1, r2, r3, r4, r5, r6]
  LamInternal _ r1 -> mapMaybe refToId [r1]
  LetInternal _ r1 r2 -> mapMaybe refToId [r1, r2]
  AppInternal _ r1 r2 -> mapMaybe refToId [r1, r2]
  LedgerAccessInternal _ r1 -> mapMaybe refToId [r1]
  LedgerDestructInternal _ r1 r2 -> mapMaybe refToId [r1, r2]

-- Helpers

refToId :: Ref -> Maybe Id
refToId = \case
  AnId i -> pure i
  _ -> Nothing

typeOfRef :: forall (m :: Type -> Type). (MonadHashCons Id ASGNode m) => Ref -> m TyASGNode
typeOfRef = \case
  AnId anId ->
    typeOfNode
      .
      -- This shouldn't fail because the existence of Id implies it's been cached by the HashCons monad.
      fromJust
      <$> lookupRef anId
  AnArg (Arg _ ty) -> pure ty
  ABound (Bound _ ty) -> pure ty

typeOfNode :: ASGNode -> TyASGNode
typeOfNode = \case
  LitInternal ty _ -> ATyExpr ty
  PrimInternal ty _ -> ty
  LamInternal ty _ -> ATyLam ty
  LetInternal ty _ _ -> ty
  AppInternal ty _ _ -> ty
  LedgerAccessInternal _ _ -> error "TODO"
  LedgerDestructInternal {} -> error "TODO"
