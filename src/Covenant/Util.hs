{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}

-- | Module: Covenant.Util
--
-- Various helpers that don't fit anywhere else.
--
-- @since 1.0.0
module Covenant.Util
  ( pattern NilV,
    pattern ConsV,
    prettyStr,
  )
where

import Data.Kind (Type)
import Data.Text qualified as Text
import Data.Vector.Generic (Vector)
import Data.Vector.Generic qualified as Vector
import Prettyprinter (Pretty (pretty), defaultLayoutOptions, layoutPretty)
import Prettyprinter.Render.Text (renderStrict)

-- | A pattern matching helper for vectors (of all types), corresponding to @[]@
-- for lists. This pattern is bidirectional, which means it can be used just
-- like a data constructor.
--
-- @since 1.0.0
pattern NilV :: forall (a :: Type) (v :: Type -> Type). (Vector v a) => v a
pattern NilV <- (Vector.uncons -> Nothing)
  where
    NilV = Vector.empty

-- | A pattern matching helper for vectors (of all types), corresponding to @x :
-- xs@-style matches. This is a read-only pattern, which means you can match
-- with it, but not construct; this is done because @cons@ for vectors is
-- inefficient and should thus be used consciously, using appropriate functions.
--
-- Together with 'NilV', 'ConsV' provides an exhaustive match.
--
-- @since 1.0.0
pattern ConsV ::
  forall (a :: Type) (v :: Type -> Type).
  (Vector v a) =>
  a ->
  v a ->
  v a
pattern ConsV x xs <- (Vector.uncons -> Just (x, xs))

{-# COMPLETE NilV, ConsV #-}

-- | Shorthand to transform any 'Pretty' into a 'String' using the default
-- layout.
--
-- @since 1.1.0
prettyStr :: forall (a :: Type). (Pretty a) => a -> String
prettyStr =
  Text.unpack
    . renderStrict
    . layoutPretty defaultLayoutOptions
    . pretty
