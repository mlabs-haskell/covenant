module Covenant.Ledger
  ( LedgerAccessor (..),
    LedgerDestructor (..),
    LedgerUnwrapAccessor (..),
    LedgerFieldAccessor (..),
  )
where

-- | @since 1.0.0
data LedgerAccessor
  = LedgerUnwrap LedgerUnwrapAccessor
  | LedgerField LedgerFieldAccessor
  deriving stock
    ( -- | @since 1.0.0
      Eq,
      -- | @since 1.0.0
      Ord,
      -- | @since 1.0.0
      Show
    )

-- | An accessor for a type with only a single field and no variants.
--
-- @since 1.0.0
data LedgerUnwrapAccessor
  = UnwrapColdCommitteeCredential
  | UnwrapHotCommitteeCredential
  | UnwrapDRepCredential
  | UnwrapConstitution
  | UnwrapChangedParameters
  deriving stock
    ( -- | @since 1.0.0
      Eq,
      -- | @since 1.0.0
      Ord,
      -- | @since 1.0.0
      Show
    )

-- | An accessor for a single-variant type with labelled fields, with a
-- different accessor per field.
--
-- @since 1.0.0
data LedgerFieldAccessor
  = FieldGovernanceActionIdTxId
  | FieldGovernanceActionIdGovActionIx
  | FieldCommitteeMembers
  | FieldCommitteeQuorum
  | FieldProtocolVersionMajor
  | FieldProtocolVersionMinor
  | FieldProposalProcedureDeposit
  | FieldProposalProcedureReturnAddr
  | FieldProposalProcedureGovernanceAction
  | FieldTxInInfoOutRef
  | FieldTxInInfoResolved
  | FieldTxInfoInputs
  | FieldTxInfoReferenceInputs
  | FieldTxInfoOutputs
  | FieldTxInfoFee
  | FieldTxInfoMint
  | FieldTxInfoTxCerts
  | FieldTxInfoWdrl
  | FieldTxInfoValidRange
  | FieldTxInfoSignatories
  | FieldTxInfoRedeemers
  | FieldTxInfoData
  | FieldTxInfoId
  | FieldTxInfoVotes
  | FieldTxInfoProposalProcedure
  | FieldTxInfoCurrentTreasuryAmount
  | FieldTxInfoTreasuryDonation
  | FieldScriptContextTxInfo
  | FieldScriptContextRedeemer
  | FieldScriptContextScriptInfo
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
