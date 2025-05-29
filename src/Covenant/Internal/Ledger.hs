module Covenant.Internal.Ledger
  ( ledgerTypes
  )
where

import Covenant.DeBruijn (DeBruijn (Z))
import Covenant.Index (Count, count0, count1, count2, ix0, ix1)
import Covenant.Type
  ( -- weirdly, can't coerece w/o importing the constructor?
    AbstractTy (BoundAt),
    BuiltinFlatT (BoolT, ByteStringT, IntegerT),
    Constructor (Constructor),
    ConstructorName (ConstructorName),
    DataDeclaration (DataDeclaration),
    DataEncoding (BuiltinStrategy, PlutusData),
    InternalStrategy (InternalAssocMapStrat, InternalDataStrat, InternalListStrat, InternalPairStrat),
    PlutusDataStrategy (ConstrData, NewtypeData),
    TyName (TyName),
    ValT (Abstraction, BuiltinFlat, Datatype),
  )
import Data.Coerce (coerce)
import Data.Vector qualified as Vector

-- All the ledger types. Just putting them in a list for now but they'll probably end up in some other kind of container eventually
ledgerTypes :: [DataDeclaration AbstractTy]
ledgerTypes = [list,
    pair,
    plutusData,
    datum,
    redeemer,
    scriptHash,
    datumHash,
    redeemerHash,
    credential,
    stakingCredential,
    pubKeyHash,
    address,
    maybeT,
    posixTime,
    interval,
    upperBound,
    lowerBound,
    extended,
    ledgerBytes,
    assocMap,
    currencySymbol,
    tokenName,
    value,
    lovelace,
    rational,
    mintValue,
    txId,
    txOutRef,
    txOut,
    outputDatum,
    txInInfo,
    dRepCredential,
    dRep,
    delegatee,
    coldCommitteeCredential,
    hotCommitteeCredential,
    txCert,
    voter,
    vote,
    governanceActionId,
    committee,
    constitution,
    changedParameters,
    protocolVersion,
    governanceAction,
    proposalProcedure,
    scriptPurpose,
    scriptInfo,
    txInfo,
    scriptContext]


-- Builtins. These aren't "real" ADTs and their unique encoding strategies indicate special handling

list :: DataDeclaration AbstractTy
list =
  mkDecl $
    Decl
      "List"
      count1
      [ Ctor "Nil" [],
        Ctor "Cons" [Abstraction (BoundAt Z ix0), tycon "List" [Abstraction (BoundAt Z ix0)]]
      ]
      (BuiltinStrategy InternalListStrat)

pair :: DataDeclaration AbstractTy
pair = mkDecl $ Decl "Pair" count2 [Ctor "Pair" [a, b]] (BuiltinStrategy InternalPairStrat)

-- Make sure this matches up with chooseData
plutusData :: DataDeclaration AbstractTy
plutusData =
  mkDecl $
    Decl
      "Data"
      count0
      [ Ctor "Constr" [BuiltinFlat IntegerT, tycon "List" [tycon "Data" []]],
        Ctor "Map" [tycon "List" [tycon "Pair" [tycon "Data" [], tycon "Data" []]]],
        Ctor "List" [tycon "List" [tycon "Data" []]],
        Ctor "I" [BuiltinFlat IntegerT],
        Ctor "B" [BuiltinFlat ByteStringT]
      ]
      (BuiltinStrategy InternalDataStrat)

-- Newtypes and Hash Types (from V1)

datum :: DataDeclaration AbstractTy
datum = mkDecl $ Decl "Datum" count0 [Ctor "Datum" [tycon "Data" []]] (PlutusData NewtypeData)

redeemer :: DataDeclaration AbstractTy
redeemer = mkDecl $ Decl "Redeemer" count0 [Ctor "Redeemer" [tycon "Data" []]] (PlutusData NewtypeData)

scriptHash :: DataDeclaration AbstractTy
scriptHash = mkDecl $ Decl "ScriptHash" count0 [Ctor "ScriptHash" [BuiltinFlat ByteStringT]] (PlutusData NewtypeData)

datumHash :: DataDeclaration AbstractTy
datumHash = mkDecl $ Decl "DatumHash" count0 [Ctor "DatumHash" [BuiltinFlat ByteStringT]] (PlutusData NewtypeData)

redeemerHash :: DataDeclaration AbstractTy
redeemerHash = mkDecl $ Decl "RedeemerHash" count0 [Ctor "RedeemerHash" [BuiltinFlat ByteStringT]] (PlutusData NewtypeData)

-- Credential + Staking Credential (from V1)
credential :: DataDeclaration AbstractTy
credential =
  mkDecl $
    Decl
      "Credential"
      count0
      [ Ctor "PubKeyCredential" [tycon "PubKeyHash" []],
        Ctor "ScriptCredential" [tycon "ScriptHash" []]
      ]
      (PlutusData ConstrData)

stakingCredential :: DataDeclaration AbstractTy
stakingCredential =
  mkDecl $
    Decl
      "StakingCredential"
      count0
      [ Ctor "StakingHash" [tycon "Credential" []],
        Ctor "StakingPtr" [BuiltinFlat IntegerT, BuiltinFlat IntegerT, BuiltinFlat IntegerT]
      ]
      (PlutusData ConstrData)

-- PubKeyHash (from V1)
pubKeyHash :: DataDeclaration AbstractTy
pubKeyHash = mkDecl $ Decl "PubKeyHash" count0 [Ctor "PubKeyHash" [BuiltinFlat ByteStringT]] (PlutusData NewtypeData)

-- Address (from V1)
address :: DataDeclaration AbstractTy
address =
  mkDecl $
    Decl
      "Address"
      count0
      [ Ctor "Address" [tycon "Credential" [], tycon "Maybe" [tycon "StakingCredential" []]]
      ]
      (PlutusData ConstrData)

-- PlutusTX types, from https://github.com/IntersectMBO/plutus/blob/master/plutus-tx/src/PlutusTx/IsData/Instances.hs
maybeT :: DataDeclaration AbstractTy
maybeT =
  mkDecl $
    Decl
      "Maybe"
      count1
      [ Ctor "Just" [Abstraction (BoundAt Z ix0)],
        Ctor "Nothing" []
      ]
      (PlutusData ConstrData)

-- Time & Intervals (V1)

posixTime :: DataDeclaration AbstractTy
posixTime = mkSimpleNewtype "POSIXTime" (BuiltinFlat IntegerT)

interval :: DataDeclaration AbstractTy
interval =
  mkDecl $
    Decl
      "Interval"
      count1
      [ Ctor
          "Interval"
          [ tycon "LowerBound" [a],
            tycon "UpperBound" [a]
          ]
      ]
      (PlutusData ConstrData)

upperBound :: DataDeclaration AbstractTy
upperBound =
  mkDecl $
    Decl
      "UpperBound"
      count1
      [ Ctor "UpperBound" [tycon "Extended" [a], BuiltinFlat BoolT]
      ]
      (PlutusData ConstrData)

lowerBound :: DataDeclaration AbstractTy
lowerBound =
  mkDecl $
    Decl
      "LowerBound"
      count1
      [ Ctor "LowerBound" [tycon "Extended" [a], BuiltinFlat BoolT]
      ]
      (PlutusData ConstrData)

extended :: DataDeclaration AbstractTy
extended =
  mkDecl $
    Decl
      "Extended"
      count1
      [ Ctor "NegInf" [],
        Ctor "Finite" [a],
        Ctor "PosInf" []
      ]
      (PlutusData ConstrData)

-- LedgerBytes (V1)

ledgerBytes :: DataDeclaration AbstractTy
ledgerBytes = mkSimpleNewtype "LedgerBytes" (BuiltinFlat ByteStringT)

-- Value & Friends (should be V1). Also AssocMap (v1)

-- NOTE Sean 5/28: This is "magical" like List/Pair/Data due to the fact that we cannot use an opaque
--                 (because opaques do not take type parameters)
assocMap :: DataDeclaration AbstractTy
assocMap =
  mkDecl $
    Decl
      "Map"
      count2
      [Ctor "Map" [tycon "List" [tycon "Pair" [a, b]]]]
      (BuiltinStrategy InternalAssocMapStrat)

currencySymbol :: DataDeclaration AbstractTy
currencySymbol = mkSimpleNewtype "CurrencySymbol" (BuiltinFlat ByteStringT)

tokenName :: DataDeclaration AbstractTy
tokenName = mkSimpleNewtype "TokenName" (BuiltinFlat ByteStringT)

value :: DataDeclaration AbstractTy
value =
  mkSimpleNewtype
    "Value"
    ( tycon
        "Map"
        [ tycon "CurrencySymbol" [],
          tycon "Map" [tycon "TokenName" [], BuiltinFlat IntegerT]
        ]
    )

lovelace :: DataDeclaration AbstractTy
lovelace = mkSimpleNewtype "LoveLance" (BuiltinFlat IntegerT)

rational :: DataDeclaration AbstractTy
rational =
  mkDecl $
    Decl
      "Rational"
      count0
      [ Ctor "Rational" [tycon "Pair" [BuiltinFlat IntegerT, BuiltinFlat IntegerT]]
      ]
      (PlutusData NewtypeData)

-- MintValue (V3)

mintValue :: DataDeclaration AbstractTy
mintValue =
  mkDecl $
    Decl
      "MintValue"
      count0
      [ Ctor
          "UnsafeMintValue"
          [ tycon
              "Map"
              [ tycon "CurrencySymbol" [],
                tycon "Map" [tycon "TokenName" [], BuiltinFlat IntegerT]
              ]
          ]
      ]
      (PlutusData NewtypeData)

-- TxId (v3)
txId :: DataDeclaration AbstractTy
txId = mkSimpleNewtype "TxId" (BuiltinFlat ByteStringT)

-- TxOutRef (v3)
txOutRef :: DataDeclaration AbstractTy
txOutRef =
  mkDecl $
    Decl
      "TxOutRef"
      count0
      [ Ctor "TxOutRef" [tycon "TxId" [], BuiltinFlat IntegerT]
      ]
      (PlutusData ConstrData)

-- TxOut (v2)
txOut :: DataDeclaration AbstractTy
txOut =
  mkDecl $
    Decl
      "TxOut"
      count0
      [ Ctor
          "TxOut"
          [ tycon "Address" [],
            tycon "Value" [],
            tycon "OutputDatum" [],
            tycon "Maybe" [tycon "ScriptHash" []]
          ]
      ]
      (PlutusData ConstrData)

-- OutputDatum (v2)
outputDatum :: DataDeclaration AbstractTy
outputDatum =
  mkDecl $
    Decl
      "OutputDatum"
      count0
      [ Ctor "NoOutputDatum" [],
        Ctor "OutputDatumHash" [tycon "DatumHash" []],
        Ctor "OutputDatum" [tycon "OutputDatum" []]
      ]
      (PlutusData ConstrData)

-- txInInfo (V3)
txInInfo :: DataDeclaration AbstractTy
txInInfo =
  mkDecl $
    Decl
      "TxInInfo"
      count0
      [ Ctor
          "TxInInfo"
          [ tycon "TxOutRef" [],
            tycon "TxOut" []
          ]
      ]
      (PlutusData ConstrData)

-- DRepCredential (v3)
dRepCredential :: DataDeclaration AbstractTy
dRepCredential = mkSimpleNewtype "DRepCredential" (tycon "Credential" [])

-- DRep (v3)
dRep :: DataDeclaration AbstractTy
dRep =
  mkDecl $
    Decl
      "DRep"
      count0
      [ Ctor "DRep" [tycon "DRepCredential" []],
        Ctor "DRepAlwaysAbstain" [],
        Ctor "DRepAlwaysNoConfidence" []
      ]
      (PlutusData ConstrData)

-- delegatee (v3)
delegatee :: DataDeclaration AbstractTy
delegatee =
  mkDecl $
    Decl
      "Delegatee"
      count0
      [ Ctor "DelegStake" [tycon "PubKeyHash" []],
        Ctor "DelegVote" [tycon "DRep" []],
        Ctor "DelegStakeVoke" [tycon "PubKeyHash" [], tycon "DRep" []]
      ]
      (PlutusData ConstrData)

coldCommitteeCredential :: DataDeclaration AbstractTy
coldCommitteeCredential = mkSimpleNewtype "ColdCommitteeCredential" (tycon "Credential" [])

hotCommitteeCredential :: DataDeclaration AbstractTy
hotCommitteeCredential = mkSimpleNewtype "HotCommitteeCredential" (tycon "Credential" [])

-- txCert (v3)
txCert :: DataDeclaration AbstractTy
txCert =
  mkDecl $
    Decl
      "TxCert"
      count0
      [ Ctor "TxCertRegStaking" [tycon "Credential" [], tycon "Maybe" [tycon "Lovelace" []]],
        Ctor "TxCertUnRegStaking" [tycon "Credential" [], tycon "Maybe" [tycon "Lovelace" []]],
        Ctor "TxCertDelegStaking" [tycon "Credential" [], tycon "Delegatee" []],
        Ctor "TxCertRegDeleg" [tycon "Credential" [], tycon "Delegatee" [], tycon "Lovelace" []],
        Ctor "TxCertRegDRep" [tycon "DRepCredential" [], tycon "Lovelace" []],
        Ctor "TxCertUpdateDRep" [tycon "DRepCredential" []],
        Ctor "TxCertUnRegDRep" [tycon "DRepCredential" [], tycon "Lovelace" []],
        Ctor "TxCertPoolRegister" [tycon "PubKeyHash" [], tycon "PubKeyHash" []],
        Ctor "TxCertPoolRetire" [tycon "PubKeyHash" [], BuiltinFlat IntegerT],
        Ctor "TxCertAuthHotCommittee" [tycon "ColdCommitteeCredential" [], tycon "HotCommitteeCredential" []],
        Ctor "TxCertResignColdCommittee" [tycon "ColdCommitteeCredential" []]
      ]
      (PlutusData ConstrData)

-- voter (v3)
voter :: DataDeclaration AbstractTy
voter =
  mkDecl $
    Decl
      "Voter"
      count0
      [ Ctor "CommitteeVoter" [tycon "HotCommitteeCredential" []],
        Ctor "DRepVoter" [tycon "DRepCredential" []],
        Ctor "StakePoolVoter" [tycon "PubKeyHash" []]
      ]
      (PlutusData ConstrData)

-- vote (v3)
vote :: DataDeclaration AbstractTy
vote =
  mkDecl $
    Decl
      "Vote"
      count0
      [ Ctor "VoteNo" [],
        Ctor "VoteYes" [],
        Ctor "Abstain" []
      ]
      (PlutusData ConstrData)

-- GovernanceActionID (v3)
governanceActionId :: DataDeclaration AbstractTy
governanceActionId =
  mkDecl $
    Decl
      "GovernanceActionId"
      count0
      [ Ctor
          "GovernanceActionId"
          [ tycon "TxId" [],
            BuiltinFlat IntegerT
          ]
      ]
      (PlutusData ConstrData)

-- Committee (v3)
committee :: DataDeclaration AbstractTy
committee =
  mkDecl $
    Decl
      "Committee"
      count0
      [ Ctor
          "Committee"
          [ tycon "Map" [tycon "ColdCommitteeCredential" [], BuiltinFlat IntegerT],
            tycon "Rational" []
          ]
      ]
      (PlutusData ConstrData)

-- constitution (V3)
constitution :: DataDeclaration AbstractTy
constitution = mkSimpleNewtype "Constitution" (tycon "Maybe" [tycon "ScriptHash" []])

-- changedParameters (V3)
changedParameters :: DataDeclaration AbstractTy
changedParameters = mkSimpleNewtype "ChangedParameters" (tycon "Data" [])

-- ProtocolVersion (V3)
protocolVersion :: DataDeclaration AbstractTy
protocolVersion =
  mkDecl $
    Decl
      "ProtocolVersion"
      count0
      [ Ctor "ProtocolVersion" [BuiltinFlat IntegerT, BuiltinFlat IntegerT]
      ]
      (PlutusData ConstrData)

-- GovernanceAction (v3)
governanceAction :: DataDeclaration AbstractTy
governanceAction =
  mkDecl $
    Decl
      "GovernanceAction"
      count0
      [ Ctor
          "ParameterChange"
          [ tycon "Maybe" [tycon "GovernanceActionId" []],
            tycon "ChangedParameters" [],
            tycon "Maybe" [tycon "ScriptHash" []]
          ],
        Ctor
          "HardForkInitiation"
          [ tycon "Maybe" [tycon "GovernanceActionId" []],
            tycon "ProtocolVersion" []
          ],
        Ctor
          "TreasuryWithdrawals"
          [ tycon "Map" [tycon "Credential" [], tycon "Lovelace" []],
            tycon "Maybe" [tycon "ScriptHash" []]
          ],
        Ctor "NoConfidence" [tycon "Maybe" [tycon "GovernanceActionId" []]],
        Ctor
          "UpdateCommittee"
          [ tycon "Maybe" [tycon "GovernanceActionId" []],
            tycon "List" [tycon "ColdCommitteeCredential" []],
            tycon "Map" [tycon "ColdCommitteeCredential" [], BuiltinFlat IntegerT],
            tycon "Rational" []
          ],
        Ctor "NewConstitution" [tycon "Maybe" [tycon "GovernanceActionId" []], tycon "Constitution" []],
        Ctor "InfoAction" []
      ]
      (PlutusData ConstrData)

-- ProposalProcedure (v3)
proposalProcedure :: DataDeclaration AbstractTy
proposalProcedure =
  mkDecl $
    Decl
      "ProposalProcedure"
      count0
      [ Ctor
          "ProposalProcedure"
          [ tycon "Lovelace" [],
            tycon "Credential" [],
            tycon "GovernanceAction" []
          ]
      ]
      (PlutusData ConstrData)

-- scriptPurpose (v3)
scriptPurpose :: DataDeclaration AbstractTy
scriptPurpose =
  mkDecl $
    Decl
      "ScriptPurpose"
      count0
      [ Ctor "Minting" [tycon "CurrencySymbol" []],
        Ctor "Spending" [tycon "TxOutRef" []],
        Ctor "Rewarding" [tycon "Credential" []],
        Ctor "Certifying" [BuiltinFlat IntegerT, tycon "TxCert" []],
        Ctor "Voting" [tycon "Voter" []],
        Ctor "Proposing" [BuiltinFlat IntegerT, tycon "ProposalProcedure" []]
      ]
      (PlutusData ConstrData)

-- ScriptInfo (V3)
scriptInfo :: DataDeclaration AbstractTy
scriptInfo =
  mkDecl $
    Decl
      "ScriptInfo"
      count0
      [ Ctor "MintingScript" [tycon "CurrencySymbol" []],
        Ctor "SpendingScript" [tycon "TxOutRef" [], tycon "Maybe" [tycon "Datum" []]],
        Ctor "RewardingScript" [tycon "Credential" []],
        Ctor "CertifyingScript" [BuiltinFlat IntegerT, tycon "TxCert" []],
        Ctor "VotingScript" [tycon "Voter" []],
        Ctor "ProposingScript" [BuiltinFlat IntegerT, tycon "ProposalProcedure" []]
      ]
      (PlutusData ConstrData)

-- This is a TypeSyn, so not a declaration, but it's *annoying* to type the ValT version out
posixTimeRange :: ValT AbstractTy
posixTimeRange = tycon "Interval" [tycon "POSIXTime" []]

-- txInfo (v3)
txInfo :: DataDeclaration AbstractTy
txInfo =
  mkDecl $
    Decl
      "TxInfo"
      count0
      [ Ctor
          "TxInfo"
          [ tycon "List" [tycon "TxInInfo" []],
            tycon "List" [tycon "TxInInfo" []],
            tycon "List" [tycon "TxOut" []],
            tycon "Lovelace" [],
            tycon "MintValue" [],
            tycon "List" [tycon "TxCert" []],
            tycon "Map" [tycon "Credential" [], tycon "Lovelace" []],
            posixTimeRange,
            tycon "List" [tycon "PubKeyHash" []],
            tycon "Map" [tycon "ScriptPurpose" [], tycon "Redeemer" []],
            tycon "Map" [tycon "DatumHash" [], tycon "Datum" []],
            tycon "TxId" [],
            tycon "Map" [tycon "Voter" [], tycon "Map" [tycon "GovernanceActionId" [], tycon "Vote" []]],
            tycon "List" [tycon "ProposalProcedure" []],
            tycon "Maybe" [tycon "Lovelace" []],
            tycon "Maybe" [tycon "Lovelace" []]
          ]
      ]
      (PlutusData ConstrData)

-- scriptContext (v3)
scriptContext :: DataDeclaration AbstractTy
scriptContext =
  mkDecl $
    Decl
      "ScriptContext"
      count0
      [ Ctor
          "ScriptContext"
          [ tycon "TxInfo" [],
            tycon "Redeemer" [],
            tycon "ScriptInfo" []
          ]
      ]
      (PlutusData ConstrData)

-- Helpers

-- Variants of DataDeclaration and Constructor that use Lists to avoid a slew of Vector.fromList cluttering up the module

data DeclBuilder = Decl TyName (Count "tyvar") [CtorBuilder] DataEncoding

data CtorBuilder = Ctor ConstructorName [ValT AbstractTy]

mkDecl :: DeclBuilder -> DataDeclaration AbstractTy
mkDecl (Decl tn cnt ctors enc) = DataDeclaration tn cnt (Vector.fromList . fmap mkCtor $ ctors) enc
  where
    mkCtor :: CtorBuilder -> Constructor AbstractTy
    mkCtor (Ctor cnm fields) = Constructor cnm (Vector.fromList fields)

tycon :: TyName -> [ValT AbstractTy] -> ValT AbstractTy
tycon tn vals = Datatype tn (Vector.fromList vals)

{- This is shorthand for a non-polymorphic newtype (i.e. a single ctor / arg type with a newtype strategy) where
   the name of the constructor is the same as the name of the type.

   This is a *very* common case and this seems useful to save extra typing.

-}
mkSimpleNewtype :: TyName -> ValT AbstractTy -> DataDeclaration AbstractTy
mkSimpleNewtype tn val = mkDecl $ Decl tn count0 [Ctor (coerce tn) [val]] (PlutusData NewtypeData)

-- obviously should not export these, solely exist to improve readability of declarations.
-- Since everything here is data-encodeable the DB index *should* always be Z & I don't think anything uses more than
-- 2 tyvars

a :: ValT AbstractTy
a = Abstraction (BoundAt Z ix0)

b :: ValT AbstractTy
b = Abstraction (BoundAt Z ix1)
