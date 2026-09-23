import semantics.TransactionFees
import semantics.TransactionCleanup

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- Priority fee per gas in the pinned transaction semantics. -/
def transactionPriorityFee (baseFee : Nat) (tx : Transaction) : UInt256 :=
  match tx with
  | .legacy data | .access data => data.gasPrice - .ofNat baseFee
  | .dynamic data | .blob data => min data.maxPriorityFeePerGas (data.maxFeePerGas - .ofNat baseFee)

/-- Effective gas price in the pinned transaction semantics. -/
def transactionGasPrice (baseFee : Nat) (tx : Transaction) : UInt256 :=
  match tx with
  | .legacy data | .access data => data.gasPrice
  | .dynamic _ | .blob _ => transactionPriorityFee baseFee tx + .ofNat baseFee

/-- Initial access lists. No account is pending deletion at transaction entry. -/
def transactionInitialSubstate (header : BlockHeader) (tx : Transaction) (sender : Address) : Substate :=
  let accessList := tx.getAccessList
  let storageKeys : List (AccountAddress × UInt256) := do
    let ⟨owner, slots⟩ ← accessList
    let slot ← slots.toList
    pure (owner, slot)
  let accessed := A0.accessedAccounts.insert sender
    |>.insert header.beneficiary
    |>.union (Batteries.RBSet.ofList (accessList.map Prod.fst) compare)
  let accounts := match tx.base.recipient with
    | some recipient => accessed.insert recipient
    | none => accessed
  { A0 with
    accessedAccounts := accounts
    accessedStorageKeys := Batteries.RBSet.ofList storageKeys Substate.storageKeysCmp }

/-- Execute the selected message or creation after the upfront fee debit. -/
noncomputable def transactionProvisional (accounts : AccountMap) (baseFee : Nat)
    (header genesis : BlockHeader) (blocks : ProcessedBlocks) (tx : Transaction) (sender : Address) :
    AccountMap × UInt256 × Substate × Bool :=
  let price := transactionGasPrice baseFee tx
  let checkpoint := transactionCheckpoint accounts sender tx.base.gasLimit price (.ofNat (calcBlobFee header tx))
  let substate := transactionInitialSubstate header tx sender
  let gas := UInt256.ofNat (tx.base.gasLimit.toNat - intrinsicGas tx)
  match tx.base.recipient with
  | none =>
    match Lambda tx.blobVersionedHashes .empty genesis blocks checkpoint checkpoint substate
        sender sender gas price tx.base.value tx.base.data 0 none header true with
    | (_, _, after, remaining, finalSubstate, accepted, _) => (after, remaining, finalSubstate, accepted)
  | some recipient =>
    match Θ tx.blobVersionedHashes .empty genesis blocks checkpoint checkpoint substate
        sender sender recipient (toExecute checkpoint recipient) gas price tx.base.value tx.base.value
        tx.base.data 0 header true with
    | (_, after, remaining, finalSubstate, accepted, _) => (after, remaining, finalSubstate, accepted)

/-- Refund gas, credit the beneficiary, and perform final account cleanup. -/
def transactionFinalAccounts (accounts : AccountMap) (sender beneficiary : Address)
    (limit remaining price priority : UInt256) (substate : Substate) : AccountMap :=
  let returned := remaining + min ((limit - remaining) / ⟨5⟩) substate.refundBalance
  transactionCleanup
    (transactionFeeCredits accounts sender beneficiary (returned * price) ((limit - returned) * priority))
    substate

end Rollup.EVM
