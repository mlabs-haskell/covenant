{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE PatternSynonyms #-}

module Covenant.Type
  ( AbsTy (..),
    LedgerT (..),
    BuiltinT (..),
    ValT (..),
    valTAbstractions,
    CompT (..),
    compTAbstractions,
    pattern (:-->),
    pattern (:--:>),
    pattern (::-->),
    pattern (::--:>),
    pattern (::--::>),
  )
where

import Control.Monad (guard)
import Data.EnumMap.Strict (EnumMap)
import Data.EnumMap.Strict qualified as EnumMap
import Data.EnumSet (EnumSet)
import Data.EnumSet qualified as EnumSet
import Data.Functor (($>))
import Data.Word (Word64)

newtype AbsTy = AbsTy Word64
  deriving (Eq, Enum, Ord) via Word64
  deriving stock (Show)

-- Note (Koz, 17/02/2025): This only covers V3.Contexts for now.
data LedgerT
  = ColdCommitteeCredentialT
  | HotCommitteeCredentialT
  | DRepCredentialT
  | DRepT
  | DelegateeT
  | TxCertT
  | VoterT
  | VoteT
  | GovernanceActionIdT
  | CommitteeT
  | ConstitutionT
  | ProtocolVersionT
  | ChangedParametersT
  | GovernanceActionT
  | ProposalProcedureT
  | ScriptPurposeT
  | ScriptInfoT
  | TxInInfoT
  | TxInfoT
  | ScriptContextT
  deriving stock (Eq, Ord, Show)

ledgerTAbstractions :: LedgerT -> EnumSet AbsTy
ledgerTAbstractions = const EnumSet.empty

data BuiltinT
  = UnitT
  | BoolT
  | IntegerT
  | StringT
  | ByteStringT
  | BLS12_381_G1_ElementT
  | BLS12_381_G2_ElementT
  | BLS12_381_MlResultT
  | DataT
  | LedgerType LedgerT
  | ListT ValT
  | PairT ValT ValT
  deriving stock (Eq, Ord, Show)

builtinTAbstractions :: BuiltinT -> EnumSet AbsTy
builtinTAbstractions = \case
  LedgerType t -> ledgerTAbstractions t
  ListT t -> valTAbstractions t
  PairT t1 t2 -> valTAbstractions t1 <> valTAbstractions t2
  _ -> EnumSet.empty

data ValT
  = BValT BuiltinT
  | ThunkT CompT
  | AbsT AbsTy
  deriving stock (Eq, Ord, Show)

valTAbstractions :: ValT -> EnumSet AbsTy
valTAbstractions = \case
  BValT bi -> builtinTAbstractions bi
  ThunkT t -> compTAbstractions t
  AbsT t -> EnumSet.singleton t

unifyValT :: ValT -> ValT -> Maybe (EnumMap AbsTy ValT)
unifyValT t1 t2 = do
  let t1Abs = valTAbstractions t1
  let t2Abs = valTAbstractions t2
  if
    -- The types are both concrete, so equality will do
    | EnumSet.null t1Abs && EnumSet.null t2Abs ->
        guard (t1 == t2) $> EnumMap.empty
    -- Only one type has any abstractions, so we use this to 'drive'
    -- unification
    | EnumSet.null t1Abs -> go EnumMap.empty t2 t1
    | EnumSet.null t2Abs -> go EnumMap.empty t1 t2
    -- Both types have abstractions
    | otherwise -> _
  where
    go :: EnumMap AbsTy ValT -> ValT -> ValT -> Maybe (EnumMap AbsTy ValT)
    go acc hasAbs noAbs = case hasAbs of
      AbsT abs -> pure $ acc <> EnumMap.singleton abs noAbs
      BValT bi -> case noAbs of
        BValT bi' -> goInner acc bi bi'
        _ -> Nothing
      ThunkT compT -> case noAbs of
        ThunkT compT' -> goThunk acc compT compT'
        _ -> Nothing
    goInner :: EnumMap AbsTy ValT -> BuiltinT -> BuiltinT -> Maybe (EnumMap AbsTy ValT)
    goInner acc hasAbs noAbs = case hasAbs of
      LedgerType t -> case noAbs of
        LedgerType t' -> guard (t == t') $> acc
        _ -> Nothing
      ListT t -> case noAbs of
        ListT t' -> go acc t t'
        _ -> Nothing
      PairT t1 t2 -> case noAbs of
        PairT t1' t2' -> go acc t1 t1' >>= \acc' -> go acc' t2 t2'
        _ -> Nothing
      _ -> guard (hasAbs == noAbs) $> acc
    goThunk :: EnumMap AbsTy ValT -> CompT -> CompT -> Maybe (EnumMap AbsTy ValT)
    goThunk acc hasAbs noAbs = case hasAbs of
      FunT argT resultT -> case noAbs of
        FunT argT' resultT' -> go acc argT argT' >>= \acc' -> goThunk acc' resultT resultT'
        _ -> Nothing
      ForallT t -> case noAbs of
        ForallT t' -> goThunk acc t t'
        _ -> Nothing
      ReturnT t -> case noAbs of
        ReturnT t' -> go acc t t'
        _ -> Nothing

data CompT
  = FunT ValT CompT
  | ForallT CompT
  | ReturnT ValT
  deriving stock (Eq, Ord, Show)

compTAbstractions :: CompT -> EnumSet AbsTy
compTAbstractions = \case
  FunT argT resultT -> valTAbstractions argT <> compTAbstractions resultT
  ForallT compT -> compTAbstractions compT
  ReturnT valT -> valTAbstractions valT

pattern (:-->) :: ValT -> CompT -> CompT
pattern x :--> y <- FunT x y
  where
    x :--> y = FunT x y

infixr 1 :-->

pattern (::-->) :: BuiltinT -> CompT -> CompT
pattern x ::--> y <- FunT (BValT x) y
  where
    x ::--> y = FunT (BValT x) y

infixr 1 ::-->

pattern (:--:>) :: ValT -> ValT -> CompT
pattern x :--:> y <- FunT x (ReturnT y)
  where
    x :--:> y = FunT x (ReturnT y)

pattern (::--:>) :: BuiltinT -> ValT -> CompT
pattern x ::--:> y <- FunT (BValT x) (ReturnT y)
  where
    x ::--:> y = FunT (BValT x) (ReturnT y)

infixr 1 ::--:>

pattern (::--::>) :: BuiltinT -> BuiltinT -> CompT
pattern x ::--::> y <- FunT (BValT x) (ReturnT (BValT y))
  where
    x ::--::> y = FunT (BValT x) (ReturnT (BValT y))

infixr 1 ::--::>
