module Covenant.Internal.ASG
  ( ASG (..),
    ASGCompiler (..),
    ASGCompileError (..),
    TypeError (..),
    ASGNeighbourhood (..),
    ASGZipper (..),
    openASGZipper,
    viewASGZipper,
    downASGZipper,
    leftASGZipper,
    rightASGZipper,
    upASGZipper,
    closeASGZipper,
    asgnLeft,
    asgnRight,
    compileASG,
    runASGCompiler,
  )
where

import Control.Monad.Except (ExceptT, MonadError, runExceptT)
import Control.Monad.HashCons (HashConsT, MonadHashCons, runHashConsT)
import Control.Monad.Identity (Identity (runIdentity))
import Control.Monad.Reader (ReaderT, ask, runReaderT)
import Covenant.Internal.ASGNode (ASGNode, ASGType, Id, childIds)
import Data.Bimap (Bimap)
import Data.Bimap qualified as Bimap
import Data.EnumMap.Strict (EnumMap)
import Data.EnumMap.Strict qualified as EnumMap
import Data.Foldable (traverse_)
import Data.Kind (Type)
import Data.Maybe (fromJust)
import Data.Vector (Vector)
import Optics.Fold (A_Fold, foldVL)
import Optics.Getter (A_Getter, to)
import Optics.Label (LabelOptic (labelOptic))

-- | A Covenant program, represented as an acyclic graph with a single source
-- node. We use the term /ASG/, standing for \'abstract syntax graph\' for this
-- concept.
--
-- @since 1.0.0
data ASG
  = ASG
      Id -- Source node reference: this is the 'starting point' of the ASG, or the 'toplevel computation'
      (EnumMap Id ASGNode)
  deriving stock
    ( -- | @since 1.0.0
      Eq,
      -- | @since 1.0.0
      Show
    )

-- | A helper monad for building up Covenant programs. In particular, this
-- enables hash consing.
--
-- @since 1.0.0
newtype ASGCompiler (a :: Type) = ASGCompiler (ExceptT ASGCompileError (HashConsT Id ASGNode Identity) a)
  deriving
    ( -- | @since 1.0.0
      Functor,
      -- | @since 1.0.0
      Applicative,
      -- | @since 1.0.0
      Monad,
      -- | @since 1.0.0
      MonadError ASGCompileError,
      -- | @since 1.0.0
      MonadHashCons Id ASGNode
    )
    via (ExceptT ASGCompileError (HashConsT Id ASGNode Identity))

-- | The errors that can occur during the construction of an ASG
--
-- @since 1.0.0
newtype ASGCompileError = ATypeError TypeError
  deriving
    ( -- | @since 1.0.0
      Eq,
      -- | @since 1.0.0
      Show
    )
    via TypeError

-- | The errors that come up while resolving types.
--
-- @since 1.0.0
data TypeError
  = -- | Tried to apply a value @f@ to @x@, but @f@ was not a lambda.
    TyErrAppNotALambda
      -- | Type of @f@.
      ASGType
  | -- | Tried to apply a value @f@ to @x@, but @x@ was not of the expected type.
    TyErrAppArgMismatch
      -- | Expected type
      ASGType
      -- | Type of @x@
      ASGType
  | -- | Tried to call a primitive function with incorrect arguments
    TyErrPrimArgMismatch
      -- | Types of expected arguments
      (Vector ASGType)
      -- | Types of provided arguments
      (Vector ASGType)
  | -- | Tried to construct where the items have different types.
    TyErrNonHomogenousList
  deriving stock
    ( -- | @since 1.0.0
      Eq,
      -- | @since 1.0.0
      Show
    )

-- | Run a computation in the ASGCompiler monad
--
-- @since 1.0.0
runASGCompiler :: ASGCompiler a -> (Either ASGCompileError a, Bimap Id ASGNode)
runASGCompiler (ASGCompiler m) =
  let hashConsM = runExceptT m
   in runIdentity $ runHashConsT hashConsM

-- | Given a hash consing computation associating 'Id's with 'ASGNode's
-- producing a \'top-level\' computation 'Id', transform it into an 'ASG'.
--
-- = Note
--
-- This currently returns a 'Maybe', because we cannot convince the type system
-- that lookups cannot 'miss' when building the ASG. In practice, if this ever
-- returns 'Nothing', something has gone very, /very/ wrong.
--
-- @since 1.0.0
compileASG ::
  forall (m :: Type -> Type).
  (Monad m) =>
  ASGCompiler Id ->
  m (Either ASGCompileError ASG)
compileASG comp =
  pure
    ( do
        let (startOrErr, binds) = runASGCompiler comp
        start <- startOrErr
        pure $ fromJust $ do
          u <- Bimap.lookup start binds
          built <- runReaderT (go start u) binds
          pure . ASG start $ built
    )
  where
    -- Note (Koz, 04/02/2025): We rely on the monoidal behaviour of `EnumMap`
    -- for accumulation here, instead of carrying around an explicit
    -- accumulator. This is normally a bit risky, as the default behaviour of
    -- `<>` on `Map`s of any flavour throws away values on key collisions.
    -- However, we know that `ASGCompiler` uses a `Bimap`, thus making key
    -- collisions impossible; therefore, we can use `<>` without concern.
    go :: Id -> ASGNode -> ReaderT (Bimap Id ASGNode) Maybe (EnumMap Id ASGNode)
    go currId currNode = do
      let currMap = EnumMap.singleton currId currNode
      children <- allChildren currNode
      traversed <- traverse (uncurry go) children
      pure . EnumMap.unions $ currMap : traversed

-- | A view of a single ASG node, as well as its left and right siblings, if
-- any. The view uses 'Id's, and is thus only meaningful in the context of some
-- 'ASG'.
--
-- = Note
--
-- This is mainly used as a \'helper type\' for 'ASGZipper', but we expose it to
-- allow accessors to be written over it.
--
-- @since 1.0.0
data ASGNeighbourhood = ASGN [Id] Id [Id]
  deriving stock
    ( -- | @since 1.0.0
      Eq
    )

-- Note (Koz, 11/02/2025): We need to write these by hand, because the TH-driven
-- derivation would produce lenses, which we don't want, as modifications to an
-- 'ASGNeighbourhood' have to be controlled to make any sense. They are written
-- in this slightly convoluted way because `LabelOptic` emits better error
-- messages when we do so: see
-- https://hackage.haskell.org/package/optics-core-0.4.1.1/docs/Optics-Label.html#g:8
-- for an explanation of why this is.

-- | The 'Id' for the node we're \'standing on\'.
--
-- @since 1.0.0
instance
  (k ~ A_Getter, a ~ Id, b ~ Id) =>
  LabelOptic "focus" k ASGNeighbourhood ASGNeighbourhood a b
  where
  {-# INLINEABLE labelOptic #-}
  labelOptic = to (\(ASGN _ x _) -> x)

-- | The 'Id's of our left siblings, if any. Earlier positions are closer to us:
-- thus, the first position is our rightmost left sibling.
--
-- @since 1.0.0
instance
  (k ~ A_Fold, a ~ Id, b ~ Id) =>
  LabelOptic "leftSiblings" k ASGNeighbourhood ASGNeighbourhood a b
  where
  {-# INLINEABLE labelOptic #-}
  labelOptic = foldVL $ \f (ASGN lefts _ _) -> traverse_ f lefts

-- | The 'Id's of our right siblings, if any. Earlier positions are closer to
-- us: thus, the first position is our leftmost right sibling.
--
-- @since 1.0.0
instance
  (k ~ A_Fold, a ~ Id, b ~ Id) =>
  LabelOptic "rightSiblings" k ASGNeighbourhood ASGNeighbourhood a b
  where
  {-# INLINEABLE labelOptic #-}
  labelOptic = foldVL $ \f (ASGN _ _ rights) -> traverse_ f rights

-- Move the tape left, assuming it can.
asgnLeft :: ASGNeighbourhood -> ASGNeighbourhood
asgnLeft t@(ASGN lefts curr rights) = case lefts of
  [] -> t -- can't move
  rightmostLeft : rest -> ASGN rest rightmostLeft (curr : rights)

-- Move the tape right, assuming it can.
asgnRight :: ASGNeighbourhood -> ASGNeighbourhood
asgnRight t@(ASGN lefts curr rights) = case rights of
  [] -> t -- can't move
  leftmostRight : rest -> ASGN (curr : lefts) leftmostRight rest

-- | A zipper for the ASG, allowing traversal.
--
-- = Note on implementation
--
-- Our view is based on a \'stack of neighbourhoods\' definition of graph
-- zippers. More specifically, we track both our parents and our position
-- relative our siblings at each level; the \'neighbourhoods\' are represented
-- by the 'ASGNeighbourhood' type. Every time we descend, we push a
-- \'neighbourhood\' to the stack, and as we ascend, we pop. Since any 'ASG' is
-- guaranteed to be a single-source DAG, this won't cause any issues: we cannot
-- \'loop back on ourselves\' and have repetition of the same parent
-- \'neighbourhood\' in the stack.
--
-- One slightly surprising result of this is that a node may have different left
-- and right siblings depending on how we traverse to it. This is a side effect
-- of hash consing and computation sharing: a node may be the child of several
-- different parents, and thus have different siblings given each parent. While
-- perhaps surprising, this doesn't pose any problems currently, as our zipper
-- is read-only (for now).
--
-- @since 1.0.0
data ASGZipper
  = ASGZipper
      (EnumMap Id ASGNode) -- references and meaning from original ASG
      [ASGNeighbourhood] -- stack of parents of the current focus, along with the position we were at when we descended
      ASGNeighbourhood -- current focus, with the left and right siblings tracked as if they were a list
  deriving stock
    ( -- | @since 1.0.0
      Eq
    )

-- | The \'neighbourhood\' of the node we are currently standing on.
--
-- @since 1.0.0
instance
  (k ~ A_Getter, a ~ ASGNeighbourhood, b ~ ASGNeighbourhood) =>
  LabelOptic "currentNeighbourhood" k ASGZipper ASGZipper a b
  where
  {-# INLINEABLE labelOptic #-}
  labelOptic = to $ \(ASGZipper _ _ x) -> x

-- | All parent \'neighbourhoods\' that we crossed to get here. Earlier
-- \'neighbourhoods\' are closer ancestors to us: thus, the first position is
-- the \'neighbourhood\' of our parent (that we passed to get here).
--
-- @since 1.0.0
instance
  (k ~ A_Fold, a ~ ASGNeighbourhood, b ~ ASGNeighbourhood) =>
  LabelOptic "parentNeighbourhoods" k ASGZipper ASGZipper a b
  where
  {-# INLINEABLE labelOptic #-}
  labelOptic = foldVL $ \f (ASGZipper _ ps _) -> traverse_ f ps

-- The mapping between 'Id' and 'ASGNode' for the graph being walked over using
-- an 'ASGZipper'.
--
-- @since 1.0.0
instance
  (k ~ A_Getter, a ~ EnumMap Id ASGNode, b ~ EnumMap Id ASGNode) =>
  LabelOptic "bindings" k ASGZipper ASGZipper a b
  where
  {-# INLINEABLE labelOptic #-}
  labelOptic = to $ \(ASGZipper b _ _) -> b

-- | Shortcut helper to get the node we are currently standing on (as an
-- 'ASGNode', not its 'Id').
--
-- @since 1.0.0
instance
  (k ~ A_Getter, a ~ ASGNode, b ~ ASGNode) =>
  LabelOptic "focus" k ASGZipper ASGZipper a b
  where
  {-# INLINEABLE labelOptic #-}
  labelOptic = to $ \(ASGZipper b _ (ASGN _ x _)) -> b EnumMap.! x

-- | \'Unzip\' an 'ASG', starting the traversal at the source node corresponding
-- to the \'toplevel\' computation.
--
-- @since 1.0.0
openASGZipper :: ASG -> ASGZipper
openASGZipper (ASG start binds) = ASGZipper binds [] . ASGN [] start $ []

-- | \'Rezip\' an 'ASG'.
--
-- = Note
--
-- As the 'ASGZipper' is currently read-only, this operation technically doesn't
-- have to exist. However, we provide it for future use, in case modification
-- becomes possible.
--
-- @since 1.0.0
closeASGZipper :: ASGZipper -> ASG
closeASGZipper z@(ASGZipper binds parents curr) = case parents of
  [] -> case curr of
    -- This only works as the ASG has a single source.
    ASGN _ currId _ -> ASG currId binds
  _ -> closeASGZipper . upASGZipper $ z

-- | View the node the 'ASGZipper' is currently focused on.
--
-- @since 1.0.0
viewASGZipper :: ASGZipper -> ASGNode
viewASGZipper (ASGZipper binds _ curr) = case curr of
  ASGN _ currId _ -> binds EnumMap.! currId

-- | Move the 'ASGZipper' to the leftmost child of the current focus, if it
-- exists; otherwise, nothing happens.
--
-- = Note
--
-- Due to the design of 'ASGNode', `let`-bound variables and function arguments
-- do not form dedicated ASG nodes. Thus, any such are not treated as siblings
-- or children, but instead as part of the node.
--
-- @since 1.0.0
downASGZipper :: ASGZipper -> ASGZipper
downASGZipper z@(ASGZipper binds parents curr) = case curr of
  t@(ASGN _ currId _) -> case childIds $ binds EnumMap.! currId of
    [] -> z -- can't go anywhere
    leftmost : rest -> ASGZipper binds (t : parents) . ASGN [] leftmost $ rest

-- | Move the 'ASGZipper' to the left sibling of the current focus, if it
-- exists. This bypasses any arguments or @let@-bindings; if no such node
-- exists, nothing happens.
--
-- @since 1.0.0
leftASGZipper :: ASGZipper -> ASGZipper
leftASGZipper (ASGZipper binds parents curr) =
  ASGZipper binds parents (asgnLeft curr)

-- | Move the 'ASGZipper' to the right sibling of the current focus, if it
-- exists; otherwise, nothing happens.
--
-- = Note
--
-- Due to the design of 'ASGNode', `let`-bound variables and function arguments
-- do not form dedicated ASG nodes. Thus, any such are not treated as siblings
-- or children, but instead as part of the node.
--
-- @since 1.0.0
rightASGZipper :: ASGZipper -> ASGZipper
rightASGZipper (ASGZipper binds parents curr) =
  ASGZipper binds parents (asgnRight curr)

-- | Move the 'ASGZipper' to the parent of the current focus, if it exists. If
-- we're at the root, nothing happens.
--
-- @since 1.0.0
upASGZipper :: ASGZipper -> ASGZipper
upASGZipper z@(ASGZipper binds parents _) = case parents of
  [] -> z -- nowhere to go
  parent : rest -> ASGZipper binds rest parent

-- Helpers

-- Retrieve all immediate children of the argument, together with their `Id`s
allChildren :: ASGNode -> ReaderT (Bimap Id ASGNode) Maybe [(Id, ASGNode)]
allChildren = traverse (\i -> ask >>= fmap (i,) . Bimap.lookup i) . childIds
