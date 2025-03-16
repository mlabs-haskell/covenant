module Covenant.Ledger
  ( LedgerAccessor (..),
    LedgerDestructor (..),
    TyLedger (..),
    LedgerNewtype (..),
    LedgerRecord (..),
    LedgerData (..),
    LedgerFieldName (..),
  )
where

-- | A way of accessing a ledger type's field(s).
--
-- @since 1.0.0
data LedgerAccessor
  = -- | For a type with a single field and a single variant, accesses that field.
    LedgerUnwrap
  | -- For a type with a single variant and multiple named fields, accesses the field named.
    LedgerField LedgerFieldName
  deriving stock
    ( -- | @since 1.0.0
      Eq,
      -- | @since 1.0.0
      Ord,
      -- | @since 1.0.0
      Show
    )

-- | All ledger types
--
-- @since 1.0.0
data TyLedger
  = ALedgerNewtype LedgerNewtype
  | ALedgerRecord LedgerRecord
  | ALedgerData LedgerData
  deriving stock
    ( -- | @since 1.0.0
      Eq,
      -- | @since 1.0.0
      Ord,
      -- | @since 1.0.0
      Show
    )

-- | All `newtype` ledger types
--
-- @since 1.0.0
data LedgerNewtype
  = ColdCommitteeCredential
  | HotCommitteeCredential
  | DRepCredential
  | ChangedParameters
  | PubKeyHash
  | Lovelace
  | CurrencySymbol
  | TokenName
  | Value
  | ScriptHash
  | DatumHash
  | Datum
  | Redeemer
  | Constitution
  | POSIXTime
  | TxId
  | MintValue
  deriving stock
    ( -- | @since 1.0.0
      Eq,
      -- | @since 1.0.0
      Ord,
      -- | @since 1.0.0
      Show
    )

-- | All ledger record types
--
-- @since 1.0.0
data LedgerRecord
  = GovernanceActionId
  | Committee
  | ProtocolVersion
  | ProposalProcedure
  | TxInInfo
  | TxInfo
  | ScriptContext
  | Address
  | Interval TyLedger
  | TxOut
  | TxOutRef
  deriving stock
    ( -- | @since 1.0.0
      Eq,
      -- | @since 1.0.0
      Ord,
      -- | @since 1.0.0
      Show
    )

-- | All ledger record field names
--
-- @since 1.0.0
data LedgerFieldName
  = GaidTxId
  | GaidGovActionIx
  | CommitteeMembers
  | CommitteeQuorum
  | PvMajor
  | PvMinor
  | PpDeposit
  | PpReturnAddr
  | PpGovernanceAction
  | TxInInfoOutRef
  | TxInInfoResolved
  | TxInfoInputs
  | TxInfoReferenceInputs
  | TxInfoOutputs
  | TxInfoFee
  | TxInfoMint
  | TxInfoTxCerts
  | TxInfoWdrl
  | TxInfoValidRange
  | TxInfoSignatories
  | TxInfoRedeemers
  | TxInfoData
  | TxInfoId
  | TxInfoVotes
  | TxInfoProposalProcedures
  | TxInfoCurrentTreasuryAmount
  | TxInfoTreasuryDonation
  | ScriptContextTxInfo
  | ScriptContextRedeemer
  | ScriptContextScriptInfo
  | AddressCredential
  | AddressStakingCredential
  | IvFrom
  | IvTo
  | TxOutAddress
  | TxOutValue
  | TxOutDatum
  | TxOutReferenceScript
  | TxOutRefId
  | TxOutRefIdx
  deriving stock
    ( -- | @since 1.0.0
      Eq,
      -- | @since 1.0.0
      Ord,
      -- | @since 1.0.0
      Show
    )

-- | Other ledger data types
--
-- @since 1.0.0
data LedgerData
  = DRep
  | Delegatee
  | TxCert
  | Voter
  | Vote
  | GovernanceAction
  | ScriptPurpose
  | ScriptInfo
  | Credential
  | StakingCredential
  | OutputDatum
  | UpperBound TyLedger
  | LowerBound TyLedger
  | Extended
  deriving stock
    ( -- | @since 1.0.0
      Eq,
      -- | @since 1.0.0
      Ord,
      -- | @since 1.0.0
      Show
    )

-- | A destructor for a sum type from the ledger.
--
-- @since 1.0.0
data LedgerDestructor
  = DestructorDRep
  | DestructorDelegatee
  | DestructorTxCert
  | DestructorVoter
  | DestructorVote
  | DestructorGovernanceAction
  | DestructorScriptPurpose
  | DestructorScriptInfo
  deriving stock
    ( -- | @since 1.0.0
      Eq,
      -- | @since 1.0.0
      Ord,
      -- | @since 1.0.0
      Show
    )
