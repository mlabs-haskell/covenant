{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}

-- |
-- Module: Covenant.Type
-- Copyright: (C) MLabs 2025
-- License: Apache 2.0
-- Maintainer: koz@mlabs.city, sean@mlabs.city
--
-- Covenant's type system and various ways to construct types.
--
-- @since 1.0.0
module Covenant.Type
  ( -- * Type abstractions
    AbstractTy (..),
    Renamed (..),

    -- * Computation types
    CompT (Comp0, Comp1, Comp2, Comp3, CompN),
    CompTBody (ReturnT, (:--:>), ArgsAndResult),
    arity,

    -- * Value types
    ValT (..),
    BuiltinFlatT (..),
    byteStringT,
    integerT,
    stringT,
    tyvar,
    boolT,
    g1T,
    g2T,
    mlResultT,
    unitT,

    -- * Renaming

    -- ** Types
    RenameError (..),
    RenameM,

    -- ** Introduction
    renameValT,
    renameCompT,

    -- ** Elimination
    runRenameM,

    -- * Type application
    TypeAppError (..),
    checkApp,
    -- Data declarations & friends
    DataDeclaration (DataDeclaration, OpaqueData),
    Constructor (Constructor),
    TyName,
    ConstructorName,
    DataEncoding (SOP, PlutusData),
    PlutusDataConstructor (PD_I, PD_B, PD_Constructor, PD_List),
    PlutusDataStrategy (EnumData, ProductListData, ConstrData, BuiltinStrategy, NewtypeData),

    -- * Datatype sanity checking
    cycleCheck,
  )
where

import Control.Monad (guard)
import Covenant.DeBruijn (DeBruijn)
import Covenant.Index
  ( Count,
    Index,
    count0,
    count1,
    count2,
    count3,
    intCount,
  )
-- re-export for tests
import Covenant.Internal.KindCheck (cycleCheck)
import Covenant.Internal.Rename
  ( RenameError
      ( InvalidAbstractionReference,
        IrrelevantAbstraction,
        UndeterminedAbstraction
      ),
    RenameM,
    renameCompT,
    renameValT,
    runRenameM,
  )
import Covenant.Internal.Type
  ( AbstractTy (BoundAt),
    BuiltinFlatT
      ( BLS12_381_G1_ElementT,
        BLS12_381_G2_ElementT,
        BLS12_381_MlResultT,
        BoolT,
        ByteStringT,
        IntegerT,
        StringT,
        UnitT
      ),
    CompT (CompT),
    CompTBody (CompTBody),
    Constructor (Constructor),
    ConstructorName,
    DataDeclaration (DataDeclaration,OpaqueData),
    DataEncoding (PlutusData, SOP),
    PlutusDataConstructor (PD_B, PD_Constructor, PD_I, PD_List),
    PlutusDataStrategy (BuiltinStrategy, ConstrData, EnumData, NewtypeData, ProductListData),
    Renamed (Rigid, Unifiable, Wildcard),
    TyName,
    ValT (Abstraction, BuiltinFlat, Datatype, ThunkT),
  )
import Covenant.Internal.Unification
  ( TypeAppError
      ( DoesNotUnify,
        ExcessArgs,
        InsufficientArgs,
        LeakingUnifiable,
        LeakingWildcard
      ),
    checkApp,
  )
import Data.Coerce (coerce)
import Data.Kind (Type)
import Data.Vector (Vector)
import Data.Vector qualified as Vector
import Data.Vector.NonEmpty (NonEmptyVector)
import Data.Vector.NonEmpty qualified as NonEmpty
import Optics.Core (preview)

-- | The body of a computation type that doesn't take any arguments and produces
-- the a result of the given value type. Use this just as you would a
-- data constructor.
--
-- = Example
--
-- * @'ReturnT' 'integerT'@ is @!Integer@
--
-- @since 1.0.0
pattern ReturnT :: forall (a :: Type). ValT a -> CompTBody a
pattern ReturnT x <- CompTBody (returnHelper -> Just x)
  where
    ReturnT x = CompTBody (NonEmpty.singleton x)

-- | Given a type of argument, and the body of another computation type,
-- construct a copy of the body, adding an extra argument of the argument type.
-- Use this just as you would a data constructor.
--
-- = Note
--
-- Together with 'ReturnT', these two patterns provide an exhaustive pattern
-- match.
--
-- = Example
--
-- * @'integerT' :--:> ReturnT 'byteStringT'@ is @Integer -> !ByteString@
--
-- @since 1.0.0
pattern (:--:>) ::
  forall (a :: Type).
  ValT a ->
  CompTBody a ->
  CompTBody a
pattern x :--:> xs <- CompTBody (arrowHelper -> Just (x, xs))
  where
    x :--:> xs = CompTBody (NonEmpty.cons x (coerce xs))

infixr 1 :--:>

-- | A view of a computation type as a 'Vector' of its argument types, together
-- with its result type. Can be used as a data constructor, and is an exhaustive
-- match.
--
-- = Example
--
-- * @'ArgsAndResult' ('Vector.fromList' ['integerT', 'integerT']) 'integerT'@
--   is @Integer -> Integer -> !Integer@
--
-- @since 1.0.0
pattern ArgsAndResult ::
  forall (a :: Type).
  Vector (ValT a) ->
  ValT a ->
  CompTBody a
pattern ArgsAndResult args result <- (argsAndResultHelper -> (args, result))
  where
    ArgsAndResult args result = CompTBody (NonEmpty.snocV args result)

{-# COMPLETE ArgsAndResult #-}

{-# COMPLETE ReturnT, (:--:>) #-}

-- | Determine the arity of a computation type: that is, how many arguments a
-- function of this type must be given.
--
-- @since 1.0.0
arity :: forall (a :: Type). CompT a -> Int
arity (CompT _ (CompTBody xs)) = NonEmpty.length xs - 1

-- | A computation type that does not bind any type variables. Use this like a
-- data constructor.
--
-- @since 1.0.0
pattern Comp0 ::
  forall (a :: Type).
  CompTBody a ->
  CompT a
pattern Comp0 xs <- (countHelper 0 -> Just xs)
  where
    Comp0 xs = CompT count0 xs

-- | A computation type that binds one type variable (that
-- is, something whose type is @forall a . ... -> ...)@. Use this like a data
-- constructor.
--
-- @since 1.0.0
pattern Comp1 ::
  forall (a :: Type).
  CompTBody a ->
  CompT a
pattern Comp1 xs <- (countHelper 1 -> Just xs)
  where
    Comp1 xs = CompT count1 xs

-- | A computation type that binds two type variables (that
-- is, something whose type is @forall a b . ... -> ...)@. Use this like a data
-- constructor.
--
-- @since 1.0.0
pattern Comp2 ::
  forall (a :: Type).
  CompTBody a ->
  CompT a
pattern Comp2 xs <- (countHelper 2 -> Just xs)
  where
    Comp2 xs = CompT count2 xs

-- | A computation type that binds three type variables
-- (that is, something whose type is @forall a b c . ... -> ...)@. Use this like
-- a data constructor.
--
-- @since 1.0.0
pattern Comp3 ::
  forall (a :: Type).
  CompTBody a ->
  CompT a
pattern Comp3 xs <- (countHelper 3 -> Just xs)
  where
    Comp3 xs = CompT count3 xs

-- | A general way to construct and deconstruct computations which bind an
-- arbitrary number of type variables. Use this like a data constructor. Unlike
-- the other @Comp@ patterns, 'CompN' is exhaustive if matched on.
--
-- @since 1.0.0
pattern CompN ::
  Count "tyvar" ->
  CompTBody AbstractTy ->
  CompT AbstractTy
pattern CompN count xs <- CompT count xs
  where
    CompN count xs = CompT count xs

{-# COMPLETE CompN #-}

-- | Helper for defining type variables.
--
-- @since 1.0.0
tyvar :: DeBruijn -> Index "tyvar" -> ValT AbstractTy
tyvar db = Abstraction . BoundAt db

-- | Helper for defining the value type of builtin bytestrings.
--
-- @since 1.0.0
byteStringT :: forall (a :: Type). ValT a
byteStringT = BuiltinFlat ByteStringT

-- | Helper for defining the value type of builtin integers.
--
-- @since 1.0.0
integerT :: forall (a :: Type). ValT a
integerT = BuiltinFlat IntegerT

-- | Helper for defining the value type of builtin strings.
--
-- @since 1.0.0
stringT :: forall (a :: Type). ValT a
stringT = BuiltinFlat StringT

-- | Helper for defining the value type of builtin booleans.
--
-- @since 1.0.0
boolT :: forall (a :: Type). ValT a
boolT = BuiltinFlat BoolT

-- | Helper for defining the value type of BLS12-381 G1 curve points.
--
-- @since 1.0.0
g1T :: forall (a :: Type). ValT a
g1T = BuiltinFlat BLS12_381_G1_ElementT

-- | Helper for defining the value type of BLS12-381 G2 curve points.
--
-- @since 1.0.0
g2T :: forall (a :: Type). ValT a
g2T = BuiltinFlat BLS12_381_G2_ElementT

-- | Helper for defining the value type of BLS12-381 multiplication results.
--
-- @since 1.0.0
mlResultT :: forall (a :: Type). ValT a
mlResultT = BuiltinFlat BLS12_381_MlResultT

-- | Helper for defining the value type of the builtin unit type.
--
-- @since 1.0.0
unitT :: forall (a :: Type). ValT a
unitT = BuiltinFlat UnitT

-- Helpers

returnHelper ::
  forall (a :: Type).
  NonEmptyVector (ValT a) ->
  Maybe (ValT a)
returnHelper xs = case NonEmpty.uncons xs of
  (y, ys) ->
    if Vector.length ys == 0
      then pure y
      else Nothing

arrowHelper ::
  forall (a :: Type).
  NonEmptyVector (ValT a) ->
  Maybe (ValT a, CompTBody a)
arrowHelper xs = case NonEmpty.uncons xs of
  (y, ys) -> (y,) . CompTBody <$> NonEmpty.fromVector ys

argsAndResultHelper ::
  forall (a :: Type).
  CompTBody a ->
  (Vector (ValT a), ValT a)
argsAndResultHelper (CompTBody xs) = NonEmpty.unsnoc xs

countHelper ::
  forall (a :: Type).
  Int ->
  CompT a ->
  Maybe (CompTBody a)
countHelper expected (CompT actual xs) = do
  expectedCount <- preview intCount expected
  guard (expectedCount == actual)
  pure xs
