module Covenant.Internal.ASG
  ( ASG (..),
    compileASG,
  )
where

import Algebra.Graph.Acyclic.AdjacencyMap
  ( AdjacencyMap,
    toAcyclic,
    vertex,
  )
import Algebra.Graph.AdjacencyMap qualified as Cyclic
import Control.Monad.State.Strict (runState)
import Covenant.Internal.ASGBuilder
  ( ASGBuilder (ASGBuilder),
    ASGBuilderState (ASGBuilderState),
  )
import Covenant.Internal.ASGNode
  ( ASGNode
      ( App,
        Lam,
        Let,
        Lit,
        Prim
      ),
    Id,
    PrimCall
      ( PrimCallOne,
        PrimCallSix,
        PrimCallThree,
        PrimCallTwo
      ),
    Ref (ABound, AnArg, AnId),
  )
import Data.Bimap (Bimap)
import Data.Bimap qualified as Bimap
import Data.Maybe (mapMaybe)

-- | A Covenant program, represented as an acyclic graph.
--
-- @since 1.0.0
data ASG = ASG (Id, ASGNode) (AdjacencyMap (Id, ASGNode))
  deriving stock
    ( -- | @since 1.0.0
      Eq,
      -- | @since 1.0.0
      Show
    )

-- | Given an 'Id' result in a builder monad, compile the computation that 'Id'
-- refers to into an 'ASG'.
--
-- @since 1.0.0
compileASG :: ASGBuilder Id -> Maybe ASG
compileASG (ASGBuilder comp) = do
  let (start, ASGBuilderState binds) = runState comp (ASGBuilderState Bimap.empty)
  if Bimap.size binds == 1
    then do
      -- This cannot fail, but the type system can't show it
      initial <- (start,) <$> Bimap.lookup start binds
      pure . ASG initial . vertex $ initial
    else do
      let asGraph = Cyclic.edges . go binds $ start
      -- This cannot fail, but the type system can't show it
      acyclic <- toAcyclic asGraph
      -- Same as above
      initial <- (start,) <$> Bimap.lookup start binds
      pure . ASG initial $ acyclic
  where
    go ::
      Bimap Id ASGNode ->
      Id ->
      [((Id, ASGNode), (Id, ASGNode))]
    go binds curr = case Bimap.lookup curr binds of
      Nothing -> []
      Just e ->
        let idList = toIdList e
            stepdown i = case Bimap.lookup i binds of
              Nothing -> []
              Just e' -> ((curr, e), (i, e')) : go binds i
         in concatMap stepdown idList

-- Helpers

toIdList :: ASGNode -> [Id]
toIdList = \case
  Lit _ -> []
  Prim p -> mapMaybe refToId $ case p of
    PrimCallOne _ r -> [r]
    PrimCallTwo _ r1 r2 -> [r1, r2]
    PrimCallThree _ r1 r2 r3 -> [r1, r2, r3]
    PrimCallSix _ r1 r2 r3 r4 r5 r6 -> [r1, r2, r3, r4, r5, r6]
  Lam body -> mapMaybe refToId [body]
  Let x body -> mapMaybe refToId [x, body]
  App f x -> mapMaybe refToId [f, x]

refToId :: Ref -> Maybe Id
refToId = \case
  AnArg _ -> Nothing
  AnId i -> Just i
  ABound _ -> Nothing
