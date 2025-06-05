module Covenant.Internal.PrettyPrint
  ( ScopeBoundary (..),
    PrettyContext (..),
    PrettyM,
    runPrettyM,
    prettyStr,
  )
where

import Control.Monad.Reader
  ( MonadReader,
    Reader,
    runReader,
  )
import Data.Kind (Type)
import Data.Map.Strict (Map)
import Data.Text qualified as T
import Data.Vector (Vector)
import Optics.Core
  ( A_Lens,
    LabelOptic (labelOptic),
    lens,
  )
import Prettyprinter
  ( Doc,
    Pretty (pretty),
    defaultLayoutOptions,
    layoutPretty,
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
