{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}

module Covenant.Type
  ( AbstractTy (..),
    Renamed (..),
    CompT (..),
    ValT (..),
    BuiltinFlatT (..),
    RenameError (..),
    renameValT,
    renameCompT,
    RenameM,
    runRenameM,
    pattern ReturnT,
    pattern (:--:>),
    TypeAppError (..),
    checkApp,
    arity,
    byteStringT,
    integerT,
    stringT,
    tyvar,
    boolT,
    g1T,
    g2T,
    mlResultT,
    comp0,
    comp1,
    comp2,
    comp3,
    unitT,
  )
where

import Covenant.DeBruijn (DeBruijn)
import Covenant.Index
  ( Index,
    count0,
    count1,
    count2,
    count3,
  )
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
    Renamed (Rigid, Unifiable, Wildcard),
    ValT (Abstraction, BuiltinFlat, ThunkT),
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
import Data.Kind (Type)
import Data.Vector qualified as Vector
import Data.Vector.NonEmpty (NonEmptyVector)
import Data.Vector.NonEmpty qualified as NonEmpty

-- | Helper for defining the \'bodies\' of computation types, without having to
-- use 'NonEmptyVector' functions.
--
-- @since 1.0.0
pattern ReturnT :: forall (a :: Type). ValT a -> NonEmptyVector (ValT a)
pattern ReturnT x <- (returnHelper -> Just x)
  where
    ReturnT x = NonEmpty.singleton x

-- | Helper for defining the \'bodies\' of computation types, without having to
-- use 'NonEmptyVector' for functions. Together with 'ReturnT', we can write:
--
-- @'CompT' count0 ('BuiltinFlat' 'IntT' ':--:>' 'ReturnT' ('BuiltinFlat' 'IntT'))@
--
-- instead of:
--
-- @'CompT' count0 ('NonEmpty.consV' ('BuiltinFlat' 'IntT') ('Vector.singleton' ('BuiltinFlat' 'IntT')))@
--
-- @since 1.0.0
pattern (:--:>) ::
  forall (a :: Type).
  ValT a ->
  NonEmptyVector (ValT a) ->
  NonEmptyVector (ValT a)
pattern x :--:> xs <- (NonEmpty.uncons -> traverse NonEmpty.fromVector -> Just (x, xs))
  where
    x :--:> xs = NonEmpty.cons x xs

infixr 1 :--:>

-- | Determine the arity of a computation type: that is, how many arguments a
-- function of this type must be given.
--
-- @since 1.0.0
arity :: forall (a :: Type). CompT a -> Int
arity (CompT _ xs) = NonEmpty.length xs - 1

-- | Helper for defining computation types that do not bind any type variables.
--
-- @since 1.0.0
comp0 :: forall (a :: Type). NonEmptyVector (ValT a) -> CompT a
comp0 = CompT count0

-- | Helper for defining a computation type that binds one type variable (that
-- is, something whose type is @forall a . ... -> ...)@.
--
-- @since 1.0.0
comp1 :: NonEmptyVector (ValT AbstractTy) -> CompT AbstractTy
comp1 = CompT count1

-- | Helper for defining a computation type that binds two type variables (that
-- is, something whose type is @forall a b . ... -> ...)@.
--
-- @since 1.0.0
comp2 :: NonEmptyVector (ValT AbstractTy) -> CompT AbstractTy
comp2 = CompT count2

-- | Helper for defining a computation type that binds three type variables
-- (that is, something whose type is @forall a b c . ... -> ...)@.
--
-- @since 1.0.0
comp3 :: NonEmptyVector (ValT AbstractTy) -> CompT AbstractTy
comp3 = CompT count3

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
