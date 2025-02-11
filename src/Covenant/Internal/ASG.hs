module Covenant.Internal.ASG
  ( ASG (..),
    Tape (..),
    ASGZipper (..),
    openASGZipper,
    viewASGZipper,
    downASGZipper,
    leftASGZipper,
    rightASGZipper,
    upASGZipper,
    closeASGZipper,
    tapeLeft,
    tapeRight,
    compileASG,
  )
where

import Control.Monad.HashCons (HashConsT, runHashConsT)
import Control.Monad.Reader (ReaderT, ask, runReaderT)
import Covenant.Internal.ASGNode (ASGNode, Id, childIds)
import Data.Bimap (Bimap)
import Data.Bimap qualified as Bimap
import Data.EnumMap.Strict (EnumMap)
import Data.EnumMap.Strict qualified as EnumMap
import Data.Kind (Type)

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

-- | @since 1.0.0
compileASG ::
  forall (m :: Type -> Type).
  (Monad m) =>
  HashConsT Id ASGNode m Id ->
  m (Maybe ASG)
compileASG comp = do
  (start, binds) <- runHashConsT comp
  pure $ do
    u <- Bimap.lookup start binds
    built <- runReaderT (go start u) binds
    pure . ASG start $ built
  where
    -- Note (Koz, 04/02/2025): We rely on the monoidal behaviour of `EnumMap`
    -- for accumulation here, instead of carrying around an explicit
    -- accumulator. This is normally a bit risky, as the default behaviour of
    -- `<>` on `Map`s of any flavour throws away values on key collisions.
    -- However, we know that `ASGBuilder` uses a `Bimap`, thus making key
    -- collisions impossible; therefore, we can use `<>` without concern.
    go :: Id -> ASGNode -> ReaderT (Bimap Id ASGNode) Maybe (EnumMap Id ASGNode)
    go currId currNode = do
      let currMap = EnumMap.singleton currId currNode
      children <- allChildren currNode
      traversed <- traverse (uncurry go) children
      pure . EnumMap.unions $ currMap : traversed

-- A list zipper, with two stacks representing 'elements to the left of the
-- current position' and 'elements to the right of the current position. We
-- specialize to `Id` here because that's all we'll need.
data Tape = Tape [Id] Id [Id]

-- Move the tape left, assuming it can.
tapeLeft :: Tape -> Tape
tapeLeft t@(Tape lefts curr rights) = case lefts of
  [] -> t -- can't move
  rightmostLeft : rest -> Tape rest rightmostLeft (curr : rights)

-- Move the tape right, assuming it can.
tapeRight :: Tape -> Tape
tapeRight t@(Tape lefts curr rights) = case rights of
  [] -> t -- can't move
  leftmostRight : rest -> Tape (curr : lefts) leftmostRight rest

-- | A zipper for the ASG, allowing traversal.
--
-- = Note on implementation
--
-- We use a \'stack of tapes\' definition of graph zippers: specifically, we
-- track our parents, as well as our position relative our siblings at each
-- level, using list zippers, which we store in a stack as we descend. Since any
-- 'ASG' is guaranteed to be a single-source DAG, this won't pose any problems,
-- as we cannot \'loop back on ourselves\'.
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
      [Tape] -- stack of parents of the current focus, along with the position we were at when we descended
      Tape -- current focus, with the left and right siblings tracked as if they were a list

-- | \'Unzip\' an 'ASG', starting the traversal at the source node corresponding
-- to the \'toplevel\' computation.
--
-- @since 1.0.0
openASGZipper :: ASG -> ASGZipper
openASGZipper (ASG start binds) = ASGZipper binds [] . Tape [] start $ []

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
    Tape _ currId _ -> ASG currId binds
  _ -> closeASGZipper . upASGZipper $ z

-- | View the node the 'ASGZipper' is currently focused on.
--
-- @since 1.0.0
viewASGZipper :: ASGZipper -> ASGNode
viewASGZipper (ASGZipper binds _ curr) = case curr of
  Tape _ currId _ -> binds EnumMap.! currId

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
  t@(Tape _ currId _) -> case childIds $ binds EnumMap.! currId of
    [] -> z -- can't go anywhere
    leftmost : rest -> ASGZipper binds (t : parents) . Tape [] leftmost $ rest

-- | Move the 'ASGZipper' to the left sibling of the current focus, if it
-- exists. This bypasses any arguments or @let@-bindings; if no such node
-- exists, nothing happens.
--
-- @since 1.0.0
leftASGZipper :: ASGZipper -> ASGZipper
leftASGZipper (ASGZipper binds parents curr) =
  ASGZipper binds parents (tapeLeft curr)

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
  ASGZipper binds parents (tapeRight curr)

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
