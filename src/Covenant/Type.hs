{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}

module Covenant.Type
  ( AbstractTy (..),
    Renamed (..),
    CompT (..),
    ValT (..),
    BuiltinFlatT (..),
    BuiltinNestedT (..),
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
    (-*-),
    tyvar,
    listT,
    boolT,
    dataT,
    g1T,
    g2T,
    mlResultT,
    comp0,
    comp1,
    comp2,
    unitT,
  )
where

import Control.Monad (foldM, unless)
import Control.Monad.Except (ExceptT, MonadError (throwError), catchError, runExceptT)
import Control.Monad.State.Strict (State, evalState, gets, modify)
import Covenant.DeBruijn (DeBruijn, asInt)
import Covenant.Index
  ( Count,
    Index,
    count0,
    count1,
    count2,
    intCount,
    intIndex,
  )
import Data.Coerce (coerce)
import Data.Functor.Classes (Eq1 (liftEq))
import Data.Kind (Type)
import Data.Map.Merge.Strict qualified as Merge
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Ord (comparing)
import Data.Tuple.Optics (_1)
import Data.Vector (Vector)
import Data.Vector qualified as Vector
import Data.Vector.NonEmpty (NonEmptyVector)
import Data.Vector.NonEmpty qualified as NonEmpty
import Data.Word (Word64)
import Optics.At (ix)
import Optics.Getter (to, view)
import Optics.Label (LabelOptic (labelOptic))
import Optics.Lens (A_Lens, lens)
import Optics.Optic ((%))
import Optics.Review (review)
import Optics.Setter (over, set)

-- | A type abstraction, using a combination of a DeBruijn index (to indicate
-- which scope it refers to) and a positional index (to indicate which bound
-- variable in that scope it refers to).
--
-- = Important note
--
-- This is a /relative/ representation: any given 'AbstractTy' could refer to
-- different things when placed in different positions in the ASG. This stems
-- from how DeBruijn indices behave: 'Z' refers to \'our immediate enclosing
-- scope\', @'S' 'Z'@ to \'one scope outside our immediate enclosing scope\',
-- etc. This can mean different things depending on what these scope(s) are.
--
-- @since 1.0.0
data AbstractTy = BoundAt DeBruijn (Index "tyvar")
  deriving stock
    ( -- | @since 1.0.0
      Eq,
      -- | @since 1.0.0
      Show
    )

-- | @since 1.0.0
data Renamed
  = -- | Set by an enclosing scope, and thus is essentially a
    -- concrete type, we just don't know which. First field is its \'true
    -- level\', second field is the positional index in that scope.
    Rigid Int (Index "tyvar")
  | -- | Can be unified with something, but must be consistent: that is, only one
    -- unification for every instance. Field is this variable's positional index;
    -- we don't need to track the scope, as only one scope contains unifiable
    -- bindings.
    Unifiable (Index "tyvar")
  | -- | /Must/ unify with everything, except with other distinct wildcards in the
    -- same scope. First field is a unique /scope/ identifier, second is the
    -- positional index within that scope. We must have unique identifiers for
    -- wildcard scopes, as wildcards unify with everything /except/ other
    -- wildcards in the same scope.
    Wildcard Word64 (Index "tyvar")
  deriving stock
    ( -- | @since 1.0.0
      Eq,
      -- | @since 1.0.0
      Ord,
      -- | @since 1.0.0
      Show
    )

-- | A computation type, with abstractions indicated by the type argument. In
-- pretty much any case imaginable, this would be either 'AbstractTy' (in the
-- ASG), or 'Renamed' (after renaming).
--
-- = Important note
--
-- This type has a \'type abstraction boundary\' just before it: the first field
-- indicates how many type variables it binds.
--
-- The /last/ entry in the 'NonEmpty' indicates the return type.
--
-- @since 1.0.0
data CompT (a :: Type) = CompT (Count "tyvar") (NonEmptyVector (ValT a))
  deriving stock
    ( -- | @since 1.0.0
      Eq,
      -- | @since 1.0.0
      Show
    )

-- Note (Koz, 04/03/2025): We use this for testing to compare for structural
-- similarity.
instance Eq1 CompT where
  {-# INLINEABLE liftEq #-}
  liftEq f (CompT abses1 xs) (CompT abses2 ys) =
    abses1 == abses2 && liftEq (liftEq f) xs ys

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

-- | A value type, with abstractions indicated by the type argument. In pretty
-- much any case imaginable, this would be either 'AbstractTy' (in the ASG) or
-- 'Renamed' (after renaming).
--
-- @ since 1.0.0
data ValT (a :: Type)
  = -- | An abstract type.
    Abstraction a
  | -- | A suspended computation.
    ThunkT (CompT a)
  | -- | A builtin type without any nesting.
    BuiltinFlat BuiltinFlatT
  | -- | A builtin type which is \'nested\'; something like lists, pairs etc.
    BuiltinNested (BuiltinNestedT a)
  deriving stock
    ( -- | @since 1.0.0
      Eq,
      -- | @since 1.0.0
      Show
    )

-- Note (Koz, 04/03/2025): We use this for testing to compare for structural
-- similarity.
instance Eq1 ValT where
  {-# INLINEABLE liftEq #-}
  liftEq f = \case
    Abstraction abs1 -> \case
      Abstraction abs2 -> f abs1 abs2
      _ -> False
    ThunkT t1 -> \case
      ThunkT t2 -> liftEq f t1 t2
      _ -> False
    BuiltinFlat t1 -> \case
      BuiltinFlat t2 -> t1 == t2
      _ -> False
    BuiltinNested t1 -> \case
      BuiltinNested t2 -> liftEq f t1 t2
      _ -> False

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

-- | Helper for defining the value type of Plutus @Data@.
--
-- @since 1.0.0
dataT :: forall (a :: Type). ValT a
dataT = BuiltinFlat DataT

-- | Helper for defining the value type of the builtin unit type.
--
-- @since 1.0.0
unitT :: forall (a :: Type). ValT a
unitT = BuiltinFlat UnitT

-- | All builtin types that are \'flat\': that is, do not have other types
-- \'nested inside them\'.
data BuiltinFlatT
  = UnitT
  | BoolT
  | IntegerT
  | StringT
  | ByteStringT
  | BLS12_381_G1_ElementT
  | BLS12_381_G2_ElementT
  | BLS12_381_MlResultT
  | DataT
  deriving stock
    ( -- | @since 1.0.0
      Eq,
      -- | @since 1.0.0
      Show
    )

-- | Builtin types which have \'nested\' types. These are lists and pairs only.
--
-- = Important note
--
-- The 'ListT' \'arm\' of this type has a \'type abstraction boundary\', similar
-- to that of 'CompT'.
--
-- While they may appear as such, these types aren't \'truly polymorphic\' (as
-- they cannot hold thunks, for example). We define these as such as this is
-- needed to type primops.
--
-- @since 1.0.0
data BuiltinNestedT (a :: Type)
  = ListT (Count "tyvar") (ValT a)
  | PairT (ValT a) (ValT a)
  deriving stock
    ( -- | @since 1.0.0
      Eq,
      -- | @since 1.0.0
      Show
    )

-- | Helper for constructing builtin pair types. These are assumed to not be
-- polymorphic: that is, their two argument 'ValT's refer to scopes outside of
-- the one that 'PairT' normally establishes.
--
-- @since 1.0.0
(-*-) :: forall (a :: Type). ValT a -> ValT a -> ValT a
t1 -*- t2 = BuiltinNested . PairT t1 $ t2

infixr 1 -*-

-- | Helper for constructing builtin list types.
--
-- @since 1.0.0
listT :: forall (a :: Type). Count "tyvar" -> ValT a -> ValT a
listT c = BuiltinNested . ListT c

-- Note (Koz, 04/03/2025): We use this for testing to compare for structural
-- similarity.
instance Eq1 BuiltinNestedT where
  {-# INLINEABLE liftEq #-}
  liftEq f = \case
    ListT abses1 t1 -> \case
      ListT abses2 t2 -> abses1 == abses2 && liftEq f t1 t2
      _ -> False
    PairT t11 t12 -> \case
      PairT t21 t22 -> liftEq f t11 t21 && liftEq f t12 t22
      _ -> False

-- Used during renaming. Contains a source of fresh indices for wildcards, as
-- well as tracking:
--
-- 1. How many variables are bound by each scope;
-- 2. Which of these variables have been noted as used; and
-- 3. A unique identifier for each scope (for wildcards).
data RenameState = RenameState Word64 (Vector (Vector Bool, Word64))
  deriving stock (Eq, Show)

-- Note (Koz, 11/04/2025): We need this field as a source of unique identifiers
-- when renaming wildcards. Wildcards are special in that they can unify with
-- anything (possibly _several_ anythings) except different wildcards in the
-- same scope as each other. For example, consider the computation type below:
--
-- (forall a b . a -> b -> !Int) -> (forall c . c -> !Int) -> String -> !Int
--
-- In particular, `a` and `c` would be defined the same way: `BoundAt Z ix0`.
-- However, while `c` and `b` could unify just fine, `a` and `b` could not.
-- Furthermore, they are identically scoped (in the sense that they're both
-- enclosed the same way), which means that, unlike rigid variables, we cannot
-- uniquely identify them just by their scoping.
--
-- Thus, we have to have to have a way to uniquely label any wildcard in such a
-- way that wildcards in the same scope, at the same level, are tagged
-- separately from wildcards in a _different_ scope at the same level. See the
-- functions `stepUpScope` and `dropDownScope` to see how we achieve this.
instance
  (k ~ A_Lens, a ~ Word64, b ~ Word64) =>
  LabelOptic "idSource" k RenameState RenameState a b
  where
  {-# INLINEABLE labelOptic #-}
  labelOptic =
    lens
      (\(RenameState x _) -> x)
      (\(RenameState _ y) x' -> RenameState x' y)

-- The 'outer' vector represents a stack of scopes. Each entry is a combination
-- of a vector of used variables (length is equal to the number of variables
-- bound by that scope), together with a unique identifier not only for that
-- scope, but also the `step` into that scope, as required by wildcard renaming.
instance
  (k ~ A_Lens, a ~ Vector (Vector Bool, Word64), b ~ Vector (Vector Bool, Word64)) =>
  LabelOptic "tracker" k RenameState RenameState a b
  where
  {-# INLINEABLE labelOptic #-}
  labelOptic =
    lens
      (\(RenameState _ y) -> y)
      (\(RenameState x _) y' -> RenameState x y')

-- Given a number of abstractions bound by a scope, modify the state to track
-- that scope.
stepUpScope :: Count "tyvar" -> RenameState -> RenameState
stepUpScope abses x =
  let fresh = view #idSource x
      absesI = review intCount abses
      -- Label (speculatively) the current scope 'step' with a unique value.
      entry = (Vector.replicate absesI False, fresh)
   in -- Ensure that our source of fresh identifiers is incremented
      over #tracker (Vector.cons entry) . set #idSource (fresh + 1) $ x

-- Stop tracking the last scope we added.
--
-- Note that, while we 'throw away' the information about (used) variables in
-- the scope, we do _not_ roll back the `idSource`. This is in fact why we have
-- to be in `State` rather than `Reader`: that change has to be persistent to
-- achieve our goal of renaming wildcards.
dropDownScope :: RenameState -> RenameState
dropDownScope = over #tracker Vector.tail

-- Given a pair of DeBruijn index and positional index for a variable, note that
-- we've seen this variable.
noteUsed :: DeBruijn -> Index "tyvar" -> RenameState -> RenameState
noteUsed scope index =
  set (#tracker % ix (asInt scope) % _1 % ix (review intIndex index)) True

-- | Ways in which the renamer can fail.
--
-- @since 1.0.0
data RenameError
  = -- | An attempt to reference an abstraction in a scope where this
    -- abstraction doesn't exist. First field is the true level, second is
    -- the index that was requested.
    --
    -- @since 1.0.0
    InvalidAbstractionReference Int (Index "tyvar")
  | -- | A value type specifies an abstraction that never gets used
    -- anywhere. For example, the type @forall a b . [a]@ has @b@
    -- irrelevant.
    --
    -- @since 1.0.0
    IrrelevantAbstraction
  | -- | A computation type specifies an abstraction which is not used
    -- by any argument. For example, the type @forall a b . a -> !(b -> !a)@
    -- has @b@ overdeterminate.
    --
    -- @since 1.0.0
    OverdeterminateAbstraction
  deriving stock (Eq, Show)

-- | A \'renaming monad\' which allows us to convert type representations from
-- ones that use /relative/ abstraction labelling to /absolute/ abstraction
-- labelling.
--
-- = Why this is necessary
--
-- Consider the following 'AbstractTy': @'BoundAtScope' 1 0@. The meaning of
-- this is relative to where in a type it is positioned: it could be bound by a
-- scope higher than our own, or something we can unify with. Because its
-- meaning (namely, what it refers to) is situational, type checking becomes
-- more difficult, although it has other advantages.
--
-- This monad allows us to convert this relative form into an absolute one. More
-- specifically, the renamer does two things:
--
-- * Ensures that any given abstraction refers to one, and /only/ one, thing;
-- and
-- * Indicates which abstractions are unifiable, and which are (effectively)
-- constant or fixed.
--
-- @since 1.0.0
newtype RenameM (a :: Type)
  = RenameM (ExceptT RenameError (State RenameState) a)
  deriving
    ( -- | @since 1.0.0
      Functor,
      -- | @since 1.0.0
      Applicative,
      -- | @since 1.0.0
      Monad
    )
    via (ExceptT RenameError (State RenameState))

-- | Execute a renaming computation.
--
-- @since 1.0.0
runRenameM ::
  forall (a :: Type).
  RenameM a -> Either RenameError a
runRenameM (RenameM comp) = evalState (runExceptT comp) . RenameState 0 $ Vector.empty

-- | Rename a computation type.
--
-- @since 1.0.0
renameCompT :: CompT AbstractTy -> RenameM (CompT Renamed)
renameCompT (CompT abses xs) = RenameM $ do
  -- Step up a scope
  modify (stepUpScope abses)
  -- Rename, but only the arguments
  renamedArgs <-
    Vector.generateM
      (NonEmpty.length xs - 1)
      (\i -> coerce . renameValT $ xs NonEmpty.! i)
  -- Check that we don't overdetermine anything
  ourAbstractions <- gets (view (#tracker % to Vector.head % _1))
  unless (Vector.and ourAbstractions) (throwError OverdeterminateAbstraction)
  -- Check result type
  renamedResult <- coerce . renameValT . NonEmpty.last $ xs
  -- Roll back state
  modify dropDownScope
  -- Rebuild and return
  pure . CompT abses . NonEmpty.snocV renamedArgs $ renamedResult

-- | Rename a value type.
--
-- @since 1.0.0
renameValT :: ValT AbstractTy -> RenameM (ValT Renamed)
renameValT = \case
  Abstraction (BoundAt scope index) ->
    Abstraction
      <$> RenameM
        ( do
            trueLevel <- gets (\x -> view (#tracker % to Vector.length) x - asInt scope)
            scopeInfo <- gets (\x -> view #tracker x Vector.!? asInt scope)
            let asIntIx = review intIndex index
            case scopeInfo of
              -- This variable is bound at a scope that encloses our starting
              -- point. Thus, this variable is rigid.
              Nothing -> pure . Rigid trueLevel $ index
              Just (varTracker, uniqueScopeId) -> case varTracker Vector.!? asIntIx of
                Nothing -> throwError . InvalidAbstractionReference trueLevel $ index
                Just beenUsed -> do
                  -- Note that we've seen this particular variable
                  unless beenUsed (modify (noteUsed scope index))
                  pure $
                    if trueLevel == 1
                      -- If the true level is 1, this is a unifiable
                      then Unifiable index
                      -- This variable is a wildcard
                      else Wildcard uniqueScopeId index
        )
  ThunkT t -> ThunkT <$> renameCompT t
  BuiltinFlat t -> pure . BuiltinFlat $ t
  BuiltinNested t ->
    BuiltinNested <$> case t of
      ListT abses t' -> RenameM $ do
        -- Step up a scope
        modify (stepUpScope abses)
        -- Rename the inner type
        renamed <- coerce . renameValT $ t'
        -- Check that we don't have anything irrelevant
        ourAbstractions <- gets (view (#tracker % to Vector.head % _1))
        unless (Vector.and ourAbstractions) (throwError IrrelevantAbstraction)
        -- Roll back state
        modify dropDownScope
        -- Rebuild and return
        pure . ListT abses $ renamed
      PairT t1 t2 -> RenameM $ do
        -- Rename t1, then t2, without any scope shifts
        renamed1 <- coerce . renameValT $ t1
        renamed2 <- coerce . renameValT $ t2
        -- Rebuild and return
        pure . PairT renamed1 $ renamed2

-- | @since 1.0.0
data TypeAppError
  = -- | The final type after all arguments are applied is @forall a . a@.
    LeakingUnifiable (Index "tyvar")
  | -- | A wildcard (thus, a skolem) escaped its scope.
    LeakingWildcard Word64 (Index "tyvar")
  | -- | We were given too many arguments.
    ExcessArgs (Vector (ValT Renamed))
  | -- | We weren't given enough arguments.
    InsufficientArgs
  | -- | The expected type (first field) and actual type (second field) do not
    -- unify.
    DoesNotUnify (ValT Renamed) (ValT Renamed)
  deriving stock
    ( -- | @since 1.0.0
      Eq,
      -- | @since 1.0.0
      Show
    )

-- | @since 1.0.0
checkApp :: CompT Renamed -> [ValT Renamed] -> Either TypeAppError (ValT Renamed)
checkApp (CompT _ xs) =
  let (curr, rest) = NonEmpty.uncons xs
   in go curr (Vector.toList rest)
  where
    go ::
      ValT Renamed ->
      [ValT Renamed] ->
      [ValT Renamed] ->
      Either TypeAppError (ValT Renamed)
    go curr = \case
      [] -> \case
        [] -> case curr of
          Abstraction (Unifiable index) -> Left . LeakingUnifiable $ index
          Abstraction (Wildcard scopeId index) -> Left . LeakingWildcard scopeId $ index
          _ -> pure curr
        args -> Left . ExcessArgs . Vector.fromList $ args
      rest -> \case
        [] -> Left InsufficientArgs
        (arg : args) -> do
          subs <- catchError (unify curr arg) (promoteUnificationError curr arg)
          case Map.foldlWithKey' (\acc index sub -> substitute index sub acc) rest subs of
            [] -> Left InsufficientArgs
            curr' : rest' -> go curr' rest' args

-- Helpers

-- Because unification is inherently recursive, if we find an error deep within
-- a type, the message will signify only the _part_ that fails to unify, not the
-- entire type. While potentially useful, this can be quite confusing,
-- especially with generated types. Thus, we use `catchError` with this
-- function, which effectively allows us to rename the types reported in
-- unification errors to whatever types 'wrap' them.
promoteUnificationError ::
  forall (a :: Type).
  ValT Renamed ->
  ValT Renamed ->
  TypeAppError ->
  Either TypeAppError a
promoteUnificationError topLevelExpected topLevelActual =
  Left . \case
    DoesNotUnify _ _ -> DoesNotUnify topLevelExpected topLevelActual
    err -> err

returnHelper ::
  forall (a :: Type).
  NonEmptyVector (ValT a) -> Maybe (ValT a)
returnHelper xs = case NonEmpty.uncons xs of
  (y, ys) ->
    if Vector.length ys == 0
      then pure y
      else Nothing

unify ::
  ValT Renamed ->
  ValT Renamed ->
  Either TypeAppError (Map (Index "tyvar") (ValT Renamed))
unify expected actual =
  catchError
    ( case expected of
        Abstraction t1 -> case t1 of
          -- Unifiables unify with everything, and require a substitutional rewrite.
          Unifiable index1 -> pure . Map.singleton index1 $ actual
          Rigid level1 index1 -> expectRigid level1 index1
          Wildcard scopeId1 index1 -> expectWildcard scopeId1 index1
        ThunkT t1 -> expectThunk t1
        BuiltinFlat t1 -> expectFlatBuiltin t1
        BuiltinNested t1 -> case t1 of
          ListT _ t1' -> expectListOf t1'
          PairT t11 t12 -> expectPairOf t11 t12
    )
    (promoteUnificationError expected actual)
  where
    unificationError :: forall (a :: Type). Either TypeAppError a
    unificationError = Left . DoesNotUnify expected $ actual
    noSubUnify :: forall (k :: Type) (a :: Type). Either TypeAppError (Map k a)
    noSubUnify = pure Map.empty
    expectRigid ::
      Int -> Index "tyvar" -> Either TypeAppError (Map (Index "tyvar") (ValT Renamed))
    -- Rigids behave identically to concrete types: they can unify with
    -- themselves, or any other abstraction, but nothing else. No substitutional
    -- rewrites are needed.
    expectRigid level1 index1 = case actual of
      Abstraction (Rigid level2 index2) ->
        if level1 == level2 && index1 == index2
          then noSubUnify
          else unificationError
      Abstraction _ -> noSubUnify
      _ -> unificationError
    expectWildcard ::
      Word64 -> Index "tyvar" -> Either TypeAppError (Map (Index "tyvar") (ValT Renamed))
    -- Wildcards can unify with unifiables, as well as themselves, but nothing
    -- else. No substitutional rewrites are needed.
    expectWildcard scopeId1 index1 = case actual of
      Abstraction (Unifiable _) -> noSubUnify
      Abstraction (Wildcard scopeId2 index2) ->
        if scopeId1 /= scopeId2 || index1 == index2
          then noSubUnify
          else unificationError
      _ -> unificationError
    expectThunk :: CompT Renamed -> Either TypeAppError (Map (Index "tyvar") (ValT Renamed))
    -- Thunks unify unconditionally with wildcards or unifiables. They unify
    -- conditionally with other thunks, provided that we can unify each argument
    -- with its counterpart in the same position, as well as their result types,
    -- without conflicts.
    expectThunk (CompT _ t1) = case actual of
      Abstraction (Rigid _ _) -> unificationError
      Abstraction _ -> noSubUnify
      ThunkT (CompT _ t2) -> do
        unless (comparing NonEmpty.length t1 t2 == EQ) unificationError
        catchError
          (foldM (\acc (l, r) -> unify l r >>= reconcile acc) Map.empty . NonEmpty.zip t1 $ t2)
          (promoteUnificationError expected actual)
      _ -> unificationError
    expectFlatBuiltin :: BuiltinFlatT -> Either TypeAppError (Map (Index "tyvar") (ValT Renamed))
    -- 'Flat' builtins are always concrete. They can unify with themselves,
    -- unifiables or wildcards, but nothing else. No substitutional rewrites are
    -- needed.
    expectFlatBuiltin t1 = case actual of
      Abstraction (Rigid _ _) -> unificationError
      Abstraction _ -> noSubUnify
      BuiltinFlat t2 ->
        if t1 == t2
          then noSubUnify
          else unificationError
      _ -> unificationError
    -- Lists can unify unconditionally with wildcards or unifiables. They can
    -- unify with other lists as long as their type parameters unify too.
    -- Substitutions may be required if the type parameter is a unifiable.
    expectListOf :: ValT Renamed -> Either TypeAppError (Map (Index "tyvar") (ValT Renamed))
    expectListOf tyParam = case actual of
      Abstraction (Rigid _ _) -> unificationError
      Abstraction _ -> noSubUnify
      BuiltinNested (ListT _ t2') ->
        catchError (unify tyParam t2') (promoteUnificationError expected actual)
      _ -> unificationError
    -- Pairs can unify unconditionally with wildcards or unifiables. They can
    -- unify with other pairs as long as each type parameter unifies with its
    -- counterpart without conflicts. Substitutions may be required if one or
    -- both type parameters are themselves unifiables.
    expectPairOf ::
      ValT Renamed -> ValT Renamed -> Either TypeAppError (Map (Index "tyvar") (ValT Renamed))
    expectPairOf tyParam1 tyParam2 = case actual of
      Abstraction (Rigid _ _) -> unificationError
      Abstraction _ -> noSubUnify
      BuiltinNested t2 -> case t2 of
        PairT t21 t22 -> do
          firstUnification <- catchError (unify tyParam1 t21) (promoteUnificationError expected actual)
          catchError (unify tyParam2 t22) (promoteUnificationError expected actual)
            >>= \res -> reconcile firstUnification res
        _ -> unificationError
      _ -> unificationError
    reconcile ::
      Map (Index "tyvar") (ValT Renamed) ->
      Map (Index "tyvar") (ValT Renamed) ->
      Either TypeAppError (Map (Index "tyvar") (ValT Renamed))
    -- Note (Koz, 14/04/2025): This utter soup means the following:
    --
    -- - If the old map and the new map don't have any overlapping assignments,
    --   just union them.
    -- - Otherwise, for any assignment to a unifiable that is present in both
    --   maps, ensure they assign to the same thing; if they do, it's fine,
    --   otherwise we have a problem.
    reconcile =
      Merge.mergeA
        Merge.preserveMissing
        Merge.preserveMissing
        (Merge.zipWithAMatched $ \_ l r -> l <$ unless (l == r) unificationError)

substitute :: Index "tyvar" -> ValT Renamed -> [ValT Renamed] -> [ValT Renamed]
substitute index toSub = fmap go
  where
    go :: ValT Renamed -> ValT Renamed
    go = \case
      Abstraction t -> case t of
        Unifiable ourIndex ->
          if ourIndex == index
            then toSub
            else Abstraction t
        _ -> Abstraction t
      ThunkT (CompT abses xs) -> ThunkT . CompT abses . fmap go $ xs
      BuiltinFlat t -> BuiltinFlat t
      BuiltinNested t -> BuiltinNested $ case t of
        ListT abses' t' -> ListT abses' . go $ t'
        PairT t1 t2 -> PairT (go t1) . go $ t2
