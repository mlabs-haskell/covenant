{-# LANGUAGE TemplateHaskell #-}

module Covenant.Internal.ASGBuilder
  ( ASGBuilderState (..),
    ASGBuilder (..),
    idOf,
    lit,
    prim,
    app,
  )
where

import Control.Monad.State.Strict (State, gets, modify')
import Covenant.Constant (AConstant)
import Covenant.Internal.ASGNode
  ( ASGNode (App, Lit, Prim),
    Id (Id),
    PrimCall,
    Ref,
  )
import Data.Bimap (Bimap)
import Data.Bimap qualified as Bimap
import Data.Kind (Type)
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
newtype ASGBuilder (a :: Type) = ASGBuilder (State ASGBuilderState a)
  deriving
    ( -- | @since 1.0.0
      Functor,
      -- | @since 1.0.0
      Applicative,
      -- | @since 1.0.0
      Monad
    )
    via (State ASGBuilderState)

-- | Construct a literal (constant) value.
--
-- @since 1.0.0
lit :: AConstant -> ASGBuilder Id
lit = idOf . Lit

-- | Construct a primitive function call.
--
-- @since 1.0.0
prim :: PrimCall -> ASGBuilder Id
prim = idOf . Prim

-- | Construct a function application. The first argument is (an expression
-- evaluating to) a function, the second argument is (an expression evaluating
-- to) an argument.
--
-- = Important note
--
-- Currently, this does not verify that the first argument is indeed a function,
-- nor that the second argument is appropriate.
app :: Ref -> Ref -> ASGBuilder Id
app f x = idOf (App f x)

-- Given a node, return its unique `Id`. If this is a node we've seen before in
-- the current `ExprBuilder` context, this `Id` will be looked up and reused;
-- otherwise, a fresh `Id` will be assigned, and the node cached to ensure we
-- have a reference to it henceforth.
idOf :: ASGNode -> ASGBuilder Id
idOf e = ASGBuilder $ do
  existingId <- gets (Bimap.lookupR e . view #binds)
  case existingId of
    Nothing -> do
      hasAnyBindings <- gets (Bimap.null . view #binds)
      newId <-
        if hasAnyBindings
          then (\(Id highest) -> Id (highest + 1)) <$> gets (fst . Bimap.findMax . view #binds)
          else pure . Id $ 0
      newId <$ modify' (over #binds (Bimap.insert newId e))
    Just nodeId -> pure nodeId
