module Covenant.Internal.PrettyPrint (prettyStr) where

import Data.Kind (Type)
import Data.Text qualified as T
import Prettyprinter
  ( Pretty (pretty),
    defaultLayoutOptions,
    layoutPretty,
  )
import Prettyprinter.Render.Text (renderStrict)

prettyStr :: forall (a :: Type). (Pretty a) => a -> String
prettyStr = T.unpack . renderStrict . layoutPretty defaultLayoutOptions . pretty
