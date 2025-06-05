module Covenant.Internal.PrettyPrint
  ( ScopeBoundary (..),
    PrettyContext (..),
    PrettyM,
    runPrettyM,
    bindVars,
    mkForall,
    lookupAbstraction,
    prettyStr,
  )
where

import Control.Monad.Reader
  ( MonadReader (local),
    Reader,
    asks,
    runReader,
  )
import Covenant.Index
  ( Count,
    Index,
    intCount,
    intIndex,
  )
import Data.Kind (Type)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Text qualified as T
import Data.Vector (Vector)
import Data.Vector qualified as Vector
import GHC.Exts (fromListN)
import Optics.At ()
import Optics.Core
  ( A_Lens,
    LabelOptic (labelOptic),
    ix,
    lens,
    over,
    preview,
    review,
    set,
    view,
    (%),
  )
import Prettyprinter
  ( Doc,
    Pretty (pretty),
    defaultLayoutOptions,
    hsep,
    layoutPretty,
    (<+>),
  )
import Prettyprinter.Render.Text (renderStrict)

prettyStr :: forall (a :: Type). (Pretty a) => a -> String
prettyStr = T.unpack . renderStrict . layoutPretty defaultLayoutOptions . pretty

newtype ScopeBoundary = ScopeBoundary Int
  deriving (Show, Eq, Ord, Num, Real, Enum, Integral) via Int

-- Keeping the field names for clarity even if we don't use them
data PrettyContext (ann :: Type)
  = PrettyContext
  { _boundIdents :: Map ScopeBoundary (Vector (Doc ann)),
    _currentScope :: ScopeBoundary,
    _varStream :: [Doc ann]
  }

instance
  (k ~ A_Lens, a ~ Map ScopeBoundary (Vector (Doc ann)), b ~ Map ScopeBoundary (Vector (Doc ann))) =>
  LabelOptic "boundIdents" k (PrettyContext ann) (PrettyContext ann) a b
  where
  {-# INLINEABLE labelOptic #-}
  labelOptic =
    lens
      (\(PrettyContext x _ _) -> x)
      (\(PrettyContext _ y z) x -> PrettyContext x y z)

instance
  (k ~ A_Lens, a ~ ScopeBoundary, b ~ ScopeBoundary) =>
  LabelOptic "currentScope" k (PrettyContext ann) (PrettyContext ann) a b
  where
  {-# INLINEABLE labelOptic #-}
  labelOptic =
    lens
      (\(PrettyContext _ x _) -> x)
      (\(PrettyContext x _ z) y -> PrettyContext x y z)

instance
  (k ~ A_Lens, a ~ [Doc ann], b ~ [Doc ann]) =>
  LabelOptic "varStream" k (PrettyContext ann) (PrettyContext ann) a b
  where
  {-# INLINEABLE labelOptic #-}
  labelOptic =
    lens
      (\(PrettyContext _ _ x) -> x)
      (\(PrettyContext x y _) z -> PrettyContext x y z)

-- Maybe make a newtype with error reporting since this can fail, but do later since *should't* fail
newtype PrettyM (ann :: Type) (a :: Type) = PrettyM (Reader (PrettyContext ann) a)
  deriving
    ( Functor,
      Applicative,
      Monad,
      MonadReader (PrettyContext ann)
    )
    via (Reader (PrettyContext ann))

runPrettyM :: forall (ann :: Type) (a :: Type). PrettyM ann a -> a
runPrettyM (PrettyM ma) = runReader ma (PrettyContext mempty 0 infiniteVars)
  where
    -- Lazily generated infinite list of variables. Will start with a, b, c...
    -- and cycle around to a1, b2, c3 etc.
    -- We could do something more sophisticated but this should work.
    infiniteVars :: [Doc ann]
    infiniteVars =
      let aToZ = ['a' .. 'z']
          intStrings = ("" <$ aToZ) <> map (show @Integer) [0 ..]
       in zipWith (\x xs -> pretty (x : xs)) aToZ intStrings

bindVars ::
  forall (ann :: Type) (a :: Type).
  Count "tyvar" ->
  (Vector (Doc ann) -> PrettyM ann a) ->
  PrettyM ann a
bindVars count' act
  | count == 0 = crossBoundary (act Vector.empty)
  | otherwise = crossBoundary $ do
      here <- asks (view #currentScope)
      withFreshVarNames count $ \newBoundVars ->
        local (over #boundIdents (Map.insert here newBoundVars)) (act newBoundVars)
  where
    -- Increment the current scope
    crossBoundary :: PrettyM ann a -> PrettyM ann a
    crossBoundary = local (over #currentScope (+ 1))
    count :: Int
    count = review intCount count'

mkForall ::
  forall (ann :: Type).
  Vector (Doc ann) ->
  Doc ann ->
  Doc ann
mkForall tvars funTyBody =
  if Vector.null tvars
    then funTyBody
    else "forall" <+> hsep (Vector.toList tvars) <> "." <+> funTyBody

lookupAbstraction :: forall (ann :: Type). Int -> Index "tyvar" -> PrettyM ann (Doc ann)
lookupAbstraction offset argIndex = do
  let scopeOffset = ScopeBoundary offset
  let argIndex' = review intIndex argIndex
  here <- asks (view #currentScope)
  asks (preview (#boundIdents % ix (here + scopeOffset) % ix argIndex')) >>= \case
    Nothing ->
      -- TODO: actual error reporting
      error $
        "Internal error: The encountered a variable at arg index "
          <> show argIndex'
          <> " with true level "
          <> show scopeOffset
          <> " but could not locate the corresponding pretty form at scope level "
          <> show here
    Just res' -> pure res'

-- Helpers

-- Generate N fresh var names and use the supplied monadic function to do something with them.
withFreshVarNames ::
  forall (ann :: Type) (a :: Type).
  Int ->
  (Vector (Doc ann) -> PrettyM ann a) ->
  PrettyM ann a
withFreshVarNames n act = do
  stream <- asks (view #varStream)
  let (used, rest) = splitAt n stream
  local (set #varStream rest) . act . fromListN n $ used
