module Covenant.Internal.Term
  ( CovenantTypeError (..),
    Id (UnsafeMkId),
    typeId,
    Arg (UnsafeMkArg),
    typeArg,
    Ref (..),
    typeRef,
    CompNodeInfo (..),
    ValNodeInfo (..),
    ASGNode (..),
    typeASGNode,
    ASGNodeType (..),
    BoundTyVar (..),
  )
where

import Control.Monad.Except (MonadError (throwError))
import Control.Monad.HashCons (MonadHashCons (lookupRef))
import Covenant.Constant (AConstant)
import Covenant.DeBruijn (DeBruijn)
import Covenant.Index (Index)
import Covenant.Internal.KindCheck (EncodingArgErr)
import Covenant.Internal.Rename (RenameError, UnRenameError)
import Covenant.Internal.Type
  ( AbstractTy,
    BuiltinFlatT,
    CompT,
    TyName,
    ValT,
  )
import Covenant.Internal.Unification (TypeAppError)
import Covenant.Prim (OneArgFunc, SixArgFunc, ThreeArgFunc, TwoArgFunc)
import Covenant.Type (ConstructorName, PlutusDataConstructor, Renamed)
import Data.Kind (Type)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Vector (Vector)
import Data.Void (Void)
import Data.Wedge (Wedge)
import Data.Word (Word64)

-- | An error that can arise during the construction of an ASG by programmatic
-- means.
--
-- @since 1.0.0
data CovenantTypeError
  = -- | An 'Id' has no corresponding node. This error should not arise under
    -- normal circumstances: the most likely explanation is that you're using an
    -- 'Id' that was made by a different ASG builder computation.
    --
    -- @since 1.0.0
    BrokenIdReference Id
  | -- | Computation-typed nodes can't be forced, but we tried anyway.
    --
    -- @since 1.0.0
    ForceCompType (CompT AbstractTy)
  | -- | Value-typed nodes that aren't thunks can't be forced, but we tried anyway.
    --
    -- @since 1.0.0
    ForceNonThunk (ValT AbstractTy)
  | -- | Error nodes can't be forced, but we tried anyway.
    --
    -- @since 1.0.0
    ForceError
  | -- | Value-typed nodes can't be thunked, but we tried anyway.
    --
    -- @since 1.0.0
    ThunkValType (ValT AbstractTy)
  | -- | Error nodes can't be thunked, but we tried anyway.
    --
    -- @since 1.0.0
    ThunkError
  | -- | Arguments can't be applied to a value-typed node, but we tried anyway.
    --
    -- @since 1.0.0
    ApplyToValType (ValT AbstractTy)
  | -- | Arguments can't be applied to error nodes, but we tried anyway.
    --
    -- @since 1.0.0
    ApplyToError
  | -- | Computation-typed nodes can't be applied as arguments, but we tried anyway.
    --
    -- @since 1.0.0
    ApplyCompType (CompT AbstractTy)
  | -- | Renaming the function in an application failed.
    --
    -- @since 1.0.0
    RenameFunctionFailed (CompT AbstractTy) RenameError
  | -- | Renaming an argument in an application failed.
    --
    -- @since 1.0.0
    RenameArgumentFailed (ValT AbstractTy) RenameError
  | -- | We failed to unify an expected argument type with the type of the
    -- argument we were actually given.
    --
    -- @since 1.0.0
    UnificationError TypeAppError
  | -- | An argument was requested that doesn't exist.
    --
    -- @since 1.0.0
    NoSuchArgument DeBruijn (Index "arg")
  | -- | Can't return a computation-typed node, but we tried anyway.
    --
    -- @since 1.0.0
    ReturnCompType (CompT AbstractTy)
  | -- | The body of a lambda results in a value-typed node, which isn't allowed.
    --
    -- @since 1.2.0
    LambdaResultsInCompType (CompT AbstractTy)
  | -- | The body of a lambda results in a computation-typed node which isn't
    -- a return, which isn't allowed.
    --
    -- @since 1.0.0
    LambdaResultsInNonReturn (CompT AbstractTy)
  | -- | A lambda body's return is wrapping an error, instead of being directly
    -- an error. This should not happen under normal circumstances and is most
    -- certainly a bug.
    --
    -- @since 1.0.0
    ReturnWrapsError
  | -- | We tried to return a computation-typed node, but this isn't allowed.
    --
    -- @since 1.0.0
    ReturnWrapsCompType (CompT AbstractTy)
  | -- | The result of an application is not what the computation being
    -- applied expected.
    --
    -- First field is the expected type, the second is what we actually got.
    --
    -- @since 1.0.0
    WrongReturnType (ValT AbstractTy) (ValT AbstractTy)
  | -- | Wraps an encoding argument mismatch error from KindCheck
    --
    -- @since 1.1.0
    EncodingError (EncodingArgErr AbstractTy)
  | -- | The first argument to a catamorphism wasn't an algebra, as
    -- it had the wrong arity.
    --
    -- @since 1.2.0
    CataAlgebraWrongArity Int
  | -- | The first argument to a catamorphism wasn't an algebra.
    --
    -- @since 1.1.0
    CataNotAnAlgebra ASGNodeType
  | -- | The second argument to a catamorphism wasn't a value type.
    --
    -- @since 1.1.0
    CataApplyToNonValT ASGNodeType
  | -- The algebra given to this catamorphism is not rigid (that is, its
    -- computation type binds variables).
    --
    -- @since 1.2.0
    CataNonRigidAlgebra (CompT AbstractTy)
  | -- | The second argument to a catamorphism is a builtin type, but not one
    -- we can eliminate with a catamorphism.
    --
    -- @since 1.1.0
    CataWrongBuiltinType BuiltinFlatT
  | -- | The second argument to a catamorphism is a value type, but not one we
    -- can eliminate with a catamorphism. Usually, this means it's a variable.
    --
    -- @since 1.1.0
    CataWrongValT (ValT AbstractTy)
  | -- | We requested a catamorphism for a type that doesn't exist.
    --
    -- @since 1.2.0
    CataNoSuchType TyName
  | -- | We requested a catamorphism for a type without a base functor.
    --
    -- @since 1.2.0
    CataNoBaseFunctorForType TyName
  | -- | The provided algebra is not suitable for the given type.
    --
    -- @since 1.1.0
    CataUnsuitable (CompT AbstractTy) (ValT AbstractTy)
  | -- | Someone attempted to construct a tyvar using a DB index or argument position
    --   which refers to a scope (or argument) that does not exist.
    --
    -- @since 1.2.0
    OutOfScopeTyVar DeBruijn (Index "tyvar")
  | -- | We failed to rename an "instantiation type" supplied to 'Covenant.ASG.app'.
    --
    -- @since 1.2.0
    FailedToRenameInstantiation RenameError
  | -- | Un-renaming failed.
    --
    -- @since 1.2.0
    UndoRenameFailure UnRenameError
  | -- | We tried to look up the 'DatatypeInfo' corresponding to a 'TyName' and came up empty handed.
    --
    -- @since 1.2.0
    TypeDoesNotExist TyName
  | -- | We tried to rename a 'DatatypeInfo' and failed.
    --
    -- @since 1.2.0
    DatatypeInfoRenameError RenameError
  | -- | We tried to look up a constructor for a given type. The type exists, but the constructor does not.
    --
    -- @since 1.2.0
    ConstructorDoesNotExistForType TyName ConstructorName
  | -- | When using the helper function to construct an introduction form, the type and constructor exist but the
    --   number of fields provided as an argument does not match the number of declared fields.
    --   The 'Int' is the /incorrect/ number of /supplied/ fields.
    --
    -- @since 1.2.0
    IntroFormWrongNumArgs TyName ConstructorName Int
  | -- | The user passed an error node as an argument to a datatype into form. We return the arguments given
    --   to 'Covenant.ASG.dataConstructor' in the error.
    --
    -- @since 1.2.0
    IntroFormErrorNodeField TyName ConstructorName (Vector Ref)
  | -- | The user tried to construct an introduction form using a Plutus @Data@ constructor not found in the
    --   opaque datatype declaration.
    --
    -- @since 1.2.0
    UndeclaredOpaquePlutusDataCtor (Set.Set PlutusDataConstructor) ConstructorName
  | -- | The user tried to construct an introduction form with a valid Plutus @Data@ constructor, but
    --   supplied a 'Covenant.ASG.Ref' to a field of the wrong type.
    --
    -- @since 1.2.0
    InvalidOpaqueField (Set.Set PlutusDataConstructor) ConstructorName [ValT Renamed]
  | -- The user tried to match on (i.e. use as a scrutinee) a node that wasn't a value.
    --
    -- @since 1.2.0
    MatchNonValTy ASGNodeType
  | -- | Internal error: we found a base functor Boehm-Berrarducci form that isn't a thunk after instantiation
    --   during pattern matching.Somehow we got a BFBB that is something other than a thunk after instantiation during pattern matching.
    --
    --   This should not normally happen: let us know if you see this error!
    --
    -- @since 1.2.0
    MatchNonThunkBBF (ValT Renamed)
  | -- | We encountered a rename error during pattern matching. This will refer
    -- to either the Boehm-Berrarducci form, or the base functor Boehm-Berrarducci form, depending on what type we tried to match.
    --
    -- @since 1.2.0
    MatchRenameBBFail RenameError
  | -- | This indicates that we encountered an error when renaming the arguments to the type constructor of the
    --   /scrutinee type/ during pattern matching. That is, if we're matching on @Either a b@, this means that
    --   either @a@ or @b@ failed to rename.
    --
    --  This should not normally happen: let us know if you see this error!
    --
    -- @since 1.2.0
    MatchRenameTyConArgFail RenameError
  | -- | A user tried to use a polymorphic handler in a pattern match, which is not currently allowed.
    --
    -- @since 1.2.0
    MatchPolymorphicHandler (ValT Renamed)
  | -- | We tried to use an error node as a pattern match handler.
    --
    -- @since 1.2.0
    MatchErrorAsHandler Ref
  | -- | The non-recursive branch of a pattern match needs a Boehm-Berrarducci form for the given type
    -- name, but it doesn't exist.
    --
    -- @since 1.2.0
    MatchNoBBForm TyName
  | -- | Someone tried to match on something that isn't a datatype.
    --
    -- @since 1.2.0
    MatchNonDatatypeScrutinee (ValT AbstractTy)
  | -- | The scrutinee is a datatype, be don't have it in our datatype dictionary.
    --
    -- @since 1.2.0
    MatchNoDatatypeInfo TyName
  | -- | We tried to get the base functor for a type in the ASG context, but the base functor does not exist.
    --   This can occur either because the type is not recursive and has no base functor, or because the type
    --   itself does not exist. It does not seem important to distinguish between the two failure cases.
    --
    -- @since 1.3.0
    BaseFunctorDoesNotExistFor TyName
  | -- | 'app' was called with a number of instantiation arguments that does not match the number of
    -- type variables bound in Count the CompT of the function to which arguments are being applied.
    -- The first Int is the  number of bound tyvars in the function type, the second is the number of
    -- instantiations supplied.
    --
    -- @since 1.3.0
    WrongNumInstantiationsInApp (CompT Renamed) Int Int
  | -- | A miscellaneous error, needed to catch various things that can go wrong during datatype preparation and
    -- deserialization.
    --
    -- @since 1.3.0
    OtherError Text
  deriving stock
    ( -- | @since 1.0.0
      Eq,
      -- | @since 1.0.0
      Show
    )

-- | A unique identifier for a node in a Covenant program.
--
-- @since 1.0.0
newtype Id
  = -- | = Important note
    --
    -- Using this constructor is /not safe/. Do not do this unless you know
    -- /exactly/ what you are doing. We expose this constructor, in a limited way,
    -- to allow for certain kinds of testing, and /absolutely nothing else ever/.
    -- Attempts to use this in ways it was not designed to /will/ break, this
    -- interface is /not/ stable, and relying on it is /not/ a good plan.
    --
    -- @since 1.3.1
    UnsafeMkId Word64
  deriving
    ( -- | @since 1.0.0
      Eq,
      -- | @since 1.0.0
      Ord,
      -- | @since 1.0.0
      Bounded,
      -- | Needed for internal reasons, even though this type class is terrible.
      --
      -- @since 1.0.0
      Enum
    )
    via Word64
  deriving stock
    ( -- | @since 1.0.0
      Show
    )

-- Get the type of an `Id`, or fail.
typeId ::
  forall (m :: Type -> Type).
  (MonadHashCons Id ASGNode m, MonadError CovenantTypeError m) =>
  Id ->
  m ASGNodeType
typeId i = do
  lookedUp <- lookupRef i
  case lookedUp of
    Nothing -> throwError . BrokenIdReference $ i
    Just node -> pure . typeASGNode $ node

-- | An argument passed to a function in a Covenant program.
--
-- @since 1.0.0
data Arg
  = -- | = Important note
    --
    -- Using this constructor is /not safe/. Do not do this unless you know
    -- /exactly/ what you are doing. We expose this constructor, in a limited way,
    -- to allow for certain kinds of testing, and /absolutely nothing else ever/.
    -- Attempts to use this in ways it was not designed to /will/ break, this
    -- interface is /not/ stable, and relying on it is /not/ a good plan.
    --
    -- @since 1.3.1
    UnsafeMkArg DeBruijn (Index "arg") (ValT AbstractTy)
  deriving stock
    ( -- | @since 1.0.0
      Eq,
      -- | @since 1.0.0
      Ord,
      -- | @since 1.0.0
      Show
    )

-- Helper to get the type of an argument.
typeArg :: Arg -> ValT AbstractTy
typeArg (UnsafeMkArg _ _ t) = t

-- | A general reference in a Covenant program.
--
-- @since 1.0.0
data Ref
  = -- | A function argument.
    --
    -- @since 1.0.0
    AnArg Arg
  | -- | A link to an ASG node.
    --
    -- @since 1.0.0
    AnId Id
  deriving stock
    ( -- | @since 1.0.0
      Eq,
      -- | @since 1.0.0
      Ord,
      -- | @since 1.0.0
      Show
    )

-- Helper for getting a type for any reference.
typeRef ::
  forall (m :: Type -> Type).
  (MonadHashCons Id ASGNode m, MonadError CovenantTypeError m) =>
  Ref ->
  m ASGNodeType
typeRef = \case
  AnArg arg -> pure . ValNodeType . typeArg $ arg
  AnId i -> typeId i

-- | Computation-term-specific node information.
--
-- @since 1.0.0
data CompNodeInfo
  = Builtin1Internal OneArgFunc
  | Builtin2Internal TwoArgFunc
  | Builtin3Internal ThreeArgFunc
  | Builtin6Internal SixArgFunc
  | LamInternal Ref
  | ForceInternal Ref
  deriving stock
    ( -- | @since 1.0.0
      Eq,
      -- | @since 1.0.0
      Ord,
      -- | @since 1.0.0
      Show
    )

-- | Value-term-specific node information.
--
-- @since 1.0.0
data ValNodeInfo
  = LitInternal AConstant
  | -- | @since 1.3.0
    AppInternal Id (Vector Ref) (Vector (Wedge BoundTyVar (ValT Void)))
  | ThunkInternal Id
  | -- | @since 1.1.0
    CataInternal Ref Ref
  | -- | @since 1.2.0
    DataConstructorInternal TyName ConstructorName (Vector Ref)
  | -- | @since 1.2.0
    MatchInternal Ref (Vector Ref)
  deriving stock
    ( -- | @since 1.0.0
      Eq,
      -- | @since 1.0.0
      Ord,
      -- | @since 1.0.0
      Show
    )

-- | A single node in a Covenant ASG. Where appropriate, these carry their
-- types.
--
-- @since 1.0.0
data ASGNode
  = -- | A computation-typed node.
    --
    -- @since 1.0.0
    ACompNode (CompT AbstractTy) CompNodeInfo
  | -- | A value-typed node
    --
    -- @since 1.0.0
    AValNode (ValT AbstractTy) ValNodeInfo
  | -- | An error node.
    --
    -- @since 1.0.0
    AnError
  deriving stock
    ( -- | @since 1.0.0
      Eq,
      -- | @since 1.0.0
      Ord,
      -- | @since 1.0.0
      Show
    )

-- | Produces the type of any ASG node.
--
-- @since 1.0.0
typeASGNode :: ASGNode -> ASGNodeType
typeASGNode = \case
  ACompNode t _ -> CompNodeType t
  AValNode t _ -> ValNodeType t
  AnError -> ErrorNodeType

-- | Helper data type representing the type of any ASG node whatsoever.
--
-- @since 1.0.0
data ASGNodeType
  = CompNodeType (CompT AbstractTy)
  | ValNodeType (ValT AbstractTy)
  | ErrorNodeType
  deriving stock
    ( -- | @since 1.0.0
      Eq,
      -- | @since 1.0.0
      Ord,
      -- | @since 1.0.0
      Show
    )

-- | Wrapper around an `Arg` that we know represents an in-scope type variable.
--
-- @since 1.2.0
data BoundTyVar = BoundTyVar DeBruijn (Index "tyvar")
  deriving stock
    ( -- @since 1.2.0
      Show,
      -- @since 1.2.0
      Eq,
      -- @since 1.2.0
      Ord
    )
