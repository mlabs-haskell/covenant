module Covenant.Internal.ASG
  ( ASG (..),
    compileASG,
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

-- | @since 1.0.0
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
