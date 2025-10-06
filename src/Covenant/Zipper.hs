{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}

-- |
-- Module: Covenant.Zipper
-- Copyright: (C) MLabs 2025
-- License: Apache 2.0
-- Maintainer: koz@mlabs.city, sean@mlabs.city
--
-- A read-only zipper for the Covenant ASG, based on an action monad.
--
-- @since 1.3.0
module Covenant.Zipper
  ( -- * Types
    ZipperAction,
    Tape (..),
    ZipperState (WorkingZipper, BrokenZipper),
    ASGZipper,

    -- * Functions

    -- ** Actions
    moveUp,
    moveDown,
    moveLeft,
    moveRight,
    resetZipper,

    -- ** Elimination
    runASGZipper,
  )
where

import Control.Monad.Action
  ( Action (StateOf, act),
    Actionable,
    MonadUpdate,
    UpdateT,
    actionable,
    runUpdateT,
  )
import Covenant.ASG
  ( ASGInternal,
    ASGNode (ACompNode, AValNode, AnError),
    Arg,
    CompNodeInfo (Force, Lam),
    Id,
    Ref (AnArg, AnId),
    ValNodeInfo (App, Cata, DataConstructor, Match, Thunk),
    nodeAt,
    topLevelId,
  )
import Covenant.Util (pattern ConsV, pattern NilV)
import Data.Functor.Identity (Identity, runIdentity)
import Data.Kind (Type)
import Data.Monoid (Endo (Endo))
import GHC.Exts (toList)

-- | A requested movement from the zipper. To build these, use dedicated smart
-- constructors in this module. You can \'chain together\' 'ZipperAction' using
-- the 'Semigroup' instance.
--
-- @since 1.3.0
newtype ZipperAction = ZipperAction (Actionable ZipperStep)
  deriving
    ( -- | @since 1.3.0
      Semigroup,
      -- | @since 1.3.0
      Monoid
    )
    via (Actionable ZipperStep)

-- | @since 1.3.0
instance Action ZipperAction where
  type StateOf ZipperAction = ZipperState
  act (ZipperAction acts) = foldMap go acts
    where
      go :: ZipperStep -> Endo ZipperState
      go =
        Endo . \case
          ZipperDown -> downStep
          ZipperUp -> upStep
          ZipperLeft -> leftStep
          ZipperRight -> rightStep
          ZipperReset -> resetStep

-- | Move towards the source of the ASG, \'back up\' along the path taken to
-- reach the current position. Will put the zipper in a broken state if used at
-- the source node.
--
-- @since 1.3.0
moveUp :: ZipperAction
moveUp = ZipperAction . actionable $ ZipperUp

-- | Move to the leftmost child of the current position. Will put the zipper in
-- a broken state if used at a sink node.
--
-- @since 1.3.0
moveDown :: ZipperAction
moveDown = ZipperAction . actionable $ ZipperDown

-- | Move to the sibling immediately to the left of the current position. Will
-- put the zipper in a broken state if used at a leftmost sibling.
--
-- @since 1.3.0
moveLeft :: ZipperAction
moveLeft = ZipperAction . actionable $ ZipperLeft

-- | Move to the sibling immediately to the right of the current position. Will
-- put the zipper in a broken state if used at a rightmost sibling.
--
-- @since 1.3.0
moveRight :: ZipperAction
moveRight = ZipperAction . actionable $ ZipperRight

-- | If the zipper is currently in a broken state, reset it to the last position
-- it was at before breaking. Otherwise, this does nothing.
--
-- @since 1.3.0
resetZipper :: ZipperAction
resetZipper = ZipperAction . actionable $ ZipperReset

-- | A \'list with a focus\', which may be of a different type to the rest. The
-- first field is \'backwards\', in that its first element is actually the
-- /furthest/ from the focus. Thus, if we have @Tape [3, 2, 1] "foo" [4, 5]@,
-- the \'list\' actually looks like this:
--
-- @[1, 2, 3, "foo", 4, 5]@
--
-- but /not/ like this:
--
-- @[3, 2, 1, "foo", 4, 5]@
--
-- @since 1.3.0
data Tape a b = Tape [a] b [a]
  deriving stock
    ( -- | @since 1.3.0
      Functor
    )

-- | The current state of the zipper, including whether it's in a broken state
-- or not, and if not in a broken state, the current position and the path taken
-- to get here.
--
-- @since 1.3.0
data ZipperState = ZipperState Bool ASGInternal [Tape Ref Id] (Tape Ref Ref)

-- | Matches on a working zipper, giving access to a stack of 'Tape's
-- representing the path taken to get here (tracking sibling positions) and the
-- current position, with the focus at either an 'Arg' or an 'ASGNode'.
--
-- Parent positions use 'Id' for the focus, as 'Arg's cannot have descendants.
--
-- @since 1.3.0
pattern WorkingZipper :: [Tape Ref Id] -> Tape Ref (Either Arg ASGNode) -> ZipperState
pattern WorkingZipper parents curr <- ZipperState False g parents (getNodeInfo g -> curr)

-- | Matches on a zipper in a broken state.
--
-- @since 1.3.0
pattern BrokenZipper :: ZipperState
pattern BrokenZipper <- ZipperState True _ _ _

{-# COMPLETE WorkingZipper, BrokenZipper #-}

-- | A \'zipper command monad\', designed to traverse an ASG. Based on an action
-- monad.
--
-- To perform zipper moves, use 'Control.Monad.Action.send' together with a
-- 'ZipperAction'. If you want to find out something about where we're standing,
-- use 'Control.Monad.Action.request', together with pattern matching on
-- 'ZipperState'.
--
-- @since 1.3.0
newtype ASGZipper (a :: Type)
  = ASGZipper (UpdateT ZipperAction Identity a)
  deriving
    ( -- | @since 1.3.0
      Functor,
      -- | @since 1.3.0
      Applicative,
      -- | @since 1.3.0
      Monad,
      -- | @since 1.3.0
      MonadUpdate ZipperAction
    )
    via (UpdateT ZipperAction Identity)

-- | Perform the stated actions to traverse over the 'ASG' given by the
-- argument.
--
-- @since 1.3.0
runASGZipper ::
  forall (a :: Type).
  ASGInternal ->
  ASGZipper a ->
  a
runASGZipper g (ASGZipper comp) =
  let i = topLevelId g
   in (\(_, _, x) -> x)
        . runIdentity
        . runUpdateT comp
        . ZipperState False g []
        . Tape [] (AnId i)
        $ []

-- Helpers

data ZipperStep = ZipperDown | ZipperUp | ZipperLeft | ZipperRight | ZipperReset
  deriving stock (Eq, Show)

downStep :: ZipperState -> ZipperState
downStep zs@(ZipperState walkedOff g parentLevels currentLevel) =
  if walkedOff
    then zs
    else case currentLevel of
      Tape lefts curr rights ->
        let miss = ZipperState True g parentLevels currentLevel
         in case curr of
              AnArg _ -> miss
              AnId i ->
                let next = ZipperState walkedOff g (Tape lefts i rights : parentLevels)
                 in case nodeAt i g of
                      ACompNode _ info -> case info of
                        Lam r -> next . Tape [] r $ []
                        Force r -> next . Tape [] r $ []
                        _ -> miss
                      AValNode _ info -> case info of
                        App f args _ -> next . Tape [] (AnId f) . toList $ args
                        Thunk f -> next . Tape [] (AnId f) $ []
                        Cata alg x -> next . Tape [] alg $ [x]
                        DataConstructor _ _ args -> case args of
                          NilV -> miss
                          ConsV arg args' -> next . Tape [] arg . toList $ args'
                        Match x handlers -> next . Tape [] x . toList $ handlers
                        _ -> miss
                      AnError -> miss

upStep :: ZipperState -> ZipperState
upStep zs@(ZipperState walkedOff g parentLevels currentLevel) =
  if walkedOff
    then zs
    else case parentLevels of
      [] -> ZipperState True g parentLevels currentLevel
      (p : ps) -> case p of
        Tape lefts curr rights -> ZipperState walkedOff g ps . Tape lefts (AnId curr) $ rights

leftStep :: ZipperState -> ZipperState
leftStep zs@(ZipperState walkedOff g parentLevels currentLevel) =
  if walkedOff
    then zs
    else case currentLevel of
      Tape lefts curr rights -> case lefts of
        [] -> ZipperState True g parentLevels currentLevel
        (l : ls) -> ZipperState walkedOff g parentLevels . Tape ls l $ curr : rights

rightStep :: ZipperState -> ZipperState
rightStep zs@(ZipperState walkedOff g parentLevels currentLevel) =
  if walkedOff
    then zs
    else case currentLevel of
      Tape lefts curr rights -> case rights of
        [] -> ZipperState True g parentLevels currentLevel
        (r : rs) -> ZipperState walkedOff g parentLevels . Tape (curr : lefts) r $ rs

resetStep :: ZipperState -> ZipperState
resetStep zs@(ZipperState walkedOff g parentLevels currentLevel) =
  if walkedOff
    then ZipperState False g parentLevels currentLevel
    else zs

getNodeInfo :: ASGInternal -> Tape Ref Ref -> Tape Ref (Either Arg ASGNode)
getNodeInfo g =
  fmap
    ( \case
        AnId i -> Right . nodeAt i $ g
        AnArg arg -> Left arg
    )
