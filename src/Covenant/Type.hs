{-# LANGUAGE PatternSynonyms #-}

module Covenant.Type
  ( AbsTy (..),
    LedgerT (..),
    BuiltinT (..),
    ValT (..),
    CompT (..),
    pattern (:-->),
    pattern (:--:>),
    pattern (::-->),
    pattern (::--:>),
    pattern (::--::>),
  )
where

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

data ValT
  = BValT BuiltinT
  | ThunkT CompT
  | AbsT AbsTy
  deriving stock (Eq, Ord, Show)

data CompT
  = FunT ValT CompT
  | ForallT CompT
  | ReturnT ValT
  deriving stock (Eq, Ord, Show)

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
