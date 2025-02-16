module Covenant.Type
  ( AbsTy (..),
    LedgerT (..),
    BuiltinT (..),
    ValT (..),
    CompT (..),
  )
where

import Data.Word (Word64)

-- | @since 1.0.0
newtype AbsTy = AbsTy Word64
  deriving
    ( -- | @since 1.0.0
      Eq,
      -- | @since 1.0.0
      Ord
    )
    via Word64
  deriving stock
    ( -- | @since 1.0.0
      Show
    )

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
  | AbsT AbsTy
  | ThunkT CompT
  deriving stock (Eq, Ord, Show)

data CompT
  = FunT ValT CompT
  | ReturnT ValT
  deriving stock (Eq, Ord, Show)
