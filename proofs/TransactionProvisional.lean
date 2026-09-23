import proofs.TransactionCalls

open Ethereum Ethereum.EVM

set_option maxRecDepth 4096

namespace Rollup.EVM

/-- Actual transaction execution preserves the rollup and the prepaid-fee world budget. -/
theorem transaction_provisional_preserves (accounts : AccountMap) (baseFee : Nat)
    (header genesis : BlockHeader) (blocks : ProcessedBlocks) (tx : Transaction) (sender self : Address)
    (keys : AccessScope)
    (ordinary : self ∉ π) (foreign : self ≠ sender)
    (bounded : tx.base.data.size < UInt256.size)
    (ready : BoundaryReady self
      (transactionCheckpoint accounts sender tx.base.gasLimit (transactionGasPrice baseFee tx)
        (.ofNat (calcBlobFee header tx))) keys)
    (safe : Safe (boundaryModel self
      (transactionCheckpoint accounts sender tx.base.gasLimit (transactionGasPrice baseFee tx)
        (.ofNat (calcBlobFee header tx))) keys))
    (nonce : ((transactionCheckpoint accounts sender tx.base.gasLimit (transactionGasPrice baseFee tx)
      (.ofNat (calcBlobFee header tx))).findD sender default).nonce ≠ ⟨0⟩)
    (funds : tx.base.value.toNat ≤ ethLedger
      (transactionCheckpoint accounts sender tx.base.gasLimit (transactionGasPrice baseFee tx)
        (.ofNat (calcBlobFee header tx))) sender)
    (scope : transactionExecutionScope accounts baseFee header genesis blocks tx sender self ⊆ keys) :
    let checkpoint := transactionCheckpoint accounts sender tx.base.gasLimit (transactionGasPrice baseFee tx)
      (.ofNat (calcBlobFee header tx))
    let result := transactionProvisional accounts baseFee header genesis blocks tx sender
    BoundaryRefines self keys checkpoint result.1 ∧ worldEth result.1 ≤ worldEth checkpoint := by
  dsimp only
  cases selected : tx.base.recipient with
  | none =>
    rw [transaction_creation_result accounts baseFee header genesis blocks tx sender selected]
    let call := transactionCreation accounts baseFee header genesis blocks tx sender
    have covered : creationExecutionScope call self ⊆ keys := by
      simpa only [transactionExecutionScope, selected] using scope
    change BoundaryRefines self keys call.accounts call.run.2.2.1 ∧
      worldEth call.run.2.2.1 ≤ worldEth call.accounts
    rcases executed : call.run with ⟨address, created, after, gas, substate, accepted, output⟩
    exact ⟨foreign_creation_refines call executed ordinary foreign ready safe nonce funds covered,
      foreign_creation_budget call executed ordinary foreign ready safe nonce funds covered⟩
  | some recipient =>
    rw [transaction_message_result accounts baseFee header genesis blocks tx sender recipient selected]
    let call := transactionMessage accounts baseFee header genesis blocks tx sender recipient
    have covered : selectedMessageScope call self ⊆ keys := by
      simpa only [transactionExecutionScope, selected] using scope
    change BoundaryRefines self keys call.accounts call.selectedRun.2.1 ∧
      worldEth call.selectedRun.2.1 ≤ worldEth call.accounts
    rcases executed : call.selectedRun with ⟨created, after, gas, substate, accepted, output⟩
    let result : MessageResult := ⟨created, after, gas, substate, accepted, output⟩
    exact ⟨selected_message_refines call result executed ordinary foreign rfl bounded ready safe funds covered,
      selected_message_budget call result executed ordinary foreign rfl bounded ready safe funds covered⟩

end Rollup.EVM
