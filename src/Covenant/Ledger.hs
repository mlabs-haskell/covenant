module Covenant.Ledger
  ( LedgerAccessor (..),
    LedgerDestructor (..),
  )
where

import Data.Text (Text)

-- | A way of accessing a ledger type's field(s).
--
-- @since 1.0.0
data LedgerAccessor
  = -- | For a type with a single field and a single variant, accesses that field.
    LedgerUnwrap
  | -- For a type with a single variant and multiple named fields, accesses the field named.
    LedgerField Text
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
