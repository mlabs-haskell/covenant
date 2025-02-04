module Covenant.Internal.ASG
  ( ASG (..),
    Tape (..),
    ASGZipper (..),
    compileASG,
    openASGZipper,
    viewASGZipper,
    downASGZipper,
    leftASGZipper,
    rightASGZipper,
    upASGZipper,
    closeASGZipper,
    tapeLeft,
    tapeRight,
  )
where

import Control.Monad.Reader (ReaderT, ask, runReaderT)
import Control.Monad.State.Strict (runState)
import Covenant.Internal.ASGBuilder
  ( ASGBuilder (ASGBuilder),
    ASGBuilderState (ASGBuilderState),
  )
import Covenant.Internal.ASGNode
  ( ASGNode
      ( AppInternal,
        LamInternal,
        LetInternal,
        LitInternal,
        PrimInternal
      ),
    Id,
    PrimCall
      ( PrimCallOne,
        PrimCallSix,
        PrimCallThree,
        PrimCallTwo
      ),
    Ref (AnId),
    childIds,
  )
import Data.Bimap (Bimap)
import Data.Bimap qualified as Bimap
import Data.EnumMap.Strict (EnumMap)
import Data.EnumMap.Strict qualified as EnumMap

-- | A Covenant program, represented as an acyclic graph.
--
-- @since 1.0.0
data ASG = ASG Id (EnumMap Id ASGNode)
  deriving stock
    ( -- | @since 1.0.0
      Eq,
      -- | @since 1.0.0
      Show
    )

-- | A zipper for the ASG, allowing traversal.
--
-- @since 1.0.0
data ASGZipper = ASGZipper (EnumMap Id ASGNode) [Tape] Tape

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
-- exists. This bypasses any arguments or @let@-bindings; if no such children
-- exist, nothing happens.
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
-- exists. This bypasses any arguments or @let@-bindings; if no such node
-- exists, nothing happens.
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

-- | Given an 'ASGBuilder' whose result is the 'Id' corresponding to the
-- \'toplevel computation\' in the desired ASG, attempt to compile to an 'ASG'.
--
-- = Note
--
-- This currently cannot fail, despite the type specifying that it can. This
-- stems from the fact that we don't statically know every lookup for every
-- 'Id'. In practice, if you ever get 'Nothing' from this, something has gone
-- very, /very/ wrong.
--
-- @since 1.0.0
compileASG :: ASGBuilder Id -> Maybe ASG
compileASG (ASGBuilder comp) = do
  let (start, ASGBuilderState binds) = runState comp (ASGBuilderState Bimap.empty)
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
    go ::
      Id ->
      ASGNode ->
      ReaderT (Bimap Id ASGNode) Maybe (EnumMap Id ASGNode)
    go currId currNode = do
      let currMap = EnumMap.singleton currId currNode
      descendants <- allDescendants currNode
      traversed <- traverse (uncurry go) descendants
      pure . EnumMap.unions $ currMap : traversed

-- Helpers

-- Essentially `mapMaybe` but in a more general environment and taking apart
-- `Ref`. We have to write it this way because a 'transformed' `mapMaybe` isn't
-- a thing.
queryAll :: [Ref] -> ReaderT (Bimap Id ASGNode) Maybe [(Id, ASGNode)]
queryAll = \case
  [] -> pure []
  r : rs -> case r of
    AnId i -> (:) . (i,) <$> (ask >>= Bimap.lookup i) <*> queryAll rs
    _ -> queryAll rs

allDescendants :: ASGNode -> ReaderT (Bimap Id ASGNode) Maybe [(Id, ASGNode)]
allDescendants = \case
  LitInternal _ -> pure []
  PrimInternal p -> case p of
    PrimCallOne _ r1 -> queryAll [r1]
    PrimCallTwo _ r1 r2 -> queryAll [r1, r2]
    PrimCallThree _ r1 r2 r3 -> queryAll [r1, r2, r3]
    PrimCallSix _ r1 r2 r3 r4 r5 r6 -> queryAll [r1, r2, r3, r4, r5, r6]
  LamInternal r -> queryAll [r]
  LetInternal rBind rBody -> queryAll [rBind, rBody]
  AppInternal rFun rArg -> queryAll [rFun, rArg]

data Tape = Tape [Id] Id [Id]

tapeLeft :: Tape -> Tape
tapeLeft t@(Tape lefts curr rights) = case lefts of
  [] -> t -- can't move
  rightmostLeft : rest -> Tape rest rightmostLeft (curr : rights)

tapeRight :: Tape -> Tape
tapeRight t@(Tape lefts curr rights) = case rights of
  [] -> t -- can't move
  leftmostRight : rest -> Tape (curr : lefts) leftmostRight rest
