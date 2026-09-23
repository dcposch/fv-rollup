import proofs.ExecutionSurvival
import proofs.TransactionBoundary

open Ethereum Ethereum.EVM

namespace Rollup.EVM

private theorem empty_created_absent (self : Address) :
    self ∉ (∅ : Batteries.RBSet AccountAddress compare) := by
  intro member
  have listed := (Batteries.RBSet.mem_iff_mem_toList
    (t := (∅ : Batteries.RBSet AccountAddress compare))).mp member
  obtain ⟨owner, member, _⟩ := listed
  exact List.not_mem_nil member

/-- A transaction cannot schedule the existing rollup for deletion. -/
theorem transaction_provisional_no_deletion (accounts : AccountMap) (baseFee : Nat)
    (header genesis : BlockHeader) (blocks : ProcessedBlocks) (tx : Transaction)
    (sender self : Address) (account : Account)
    (found : accounts.find? sender = some account)
    (pinned : (accounts.findD self default).code = runtimeBytecode) :
    self ∉ (transactionProvisional accounts baseFee header genesis blocks tx sender).2.2.1.selfDestructSet := by
  have checkpoint :
      (transactionCheckpoint accounts sender tx.base.gasLimit (transactionGasPrice baseFee tx)
        (.ofNat (calcBlobFee header tx)) |>.findD self default).code = runtimeBytecode :=
    (checkpoint_storage accounts sender self account tx.base.gasLimit (transactionGasPrice baseFee tx)
      (.ofNat (calcBlobFee header tx)) found).2.2.symm.trans pinned
  have absent : self ∉ (transactionInitialSubstate header tx sender).selfDestructSet := by
    rw [transaction_initial_deletions]
    exact empty_created_absent self
  cases selected : tx.base.recipient with
  | none =>
    rw [transaction_creation_result accounts baseFee header genesis blocks tx sender selected]
    let call := transactionCreation accounts baseFee header genesis blocks tx sender
    have initial : AccountSurvives self call.accounts call.created call.substate :=
      ⟨checkpoint, empty_created_absent self, absent⟩
    exact AccountSurvives.notDeleted
      (creation_survives call initial (rfl : call.run = call.run))
  | some recipient =>
    rw [transaction_message_result accounts baseFee header genesis blocks tx sender recipient selected]
    let call := transactionMessage accounts baseFee header genesis blocks tx sender recipient
    have initial : AccountSurvives self call.accounts call.created call.substate :=
      ⟨checkpoint, empty_created_absent self, absent⟩
    exact AccountSurvives.notDeleted
      (selected_message_survives call initial (rfl : call.selectedRun = call.selectedRun))

/-- Complete transactions preserve the rollup boundary, including fees and deletion cleanup. -/
theorem transaction_boundary (accounts after : AccountMap) (baseFee : Nat)
    (header genesis : BlockHeader) (blocks : ProcessedBlocks) (tx : Transaction)
    (sender self : Address) (account : Account) (keys : AccessScope)
    (finalSubstate : Substate) (accepted : Bool) (gas : UInt256)
    (found : accounts.find? sender = some account)
    (ordinary : self ∉ π) (foreign : self ≠ sender)
    (nonceBound : account.nonce.toNat < 2 ^ 64 - 1)
    (priceBound : baseFee ≤ (transactionFeeCap tx).toNat)
    (funded : tx.base.gasLimit.toNat * (transactionGasPrice baseFee tx).toNat +
      calcBlobFee header tx + tx.base.value.toNat ≤ account.balance.toNat)
    (bounded : tx.base.data.size < UInt256.size)
    (ready : BoundaryReady self accounts keys) (safe : Safe (boundaryModel self accounts keys))
    (scope : transactionExecutionScope accounts baseFee header genesis blocks tx sender self ⊆ keys)
    (executed : Υ accounts baseFee header genesis blocks tx sender = .ok (after, finalSubstate, accepted, gas)) :
    BoundaryRefines self keys accounts after :=
  transaction_boundary_of_no_deletion accounts after baseFee header genesis blocks tx sender self account keys
    finalSubstate accepted gas found ordinary foreign nonceBound priceBound funded bounded ready safe scope
    (transaction_provisional_no_deletion accounts baseFee header genesis blocks tx sender self account found
      (BoundaryReady.pinned ready)) executed

end Rollup.EVM
