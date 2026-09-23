import semantics.TransactionCalls
import semantics.TransactionExecution
import proofs.SurroundingBudget

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- The transaction's message branch is the exact selected EVM message. -/
theorem transaction_message_result (accounts : AccountMap) (baseFee : Nat)
    (header genesis : BlockHeader) (blocks : ProcessedBlocks) (tx : Transaction) (sender recipient : Address)
    (selected : tx.base.recipient = some recipient) :
    transactionProvisional accounts baseFee header genesis blocks tx sender =
      let result := (transactionMessage accounts baseFee header genesis blocks tx sender recipient).selectedRun
      (result.2.1, result.2.2.1, result.2.2.2.1, result.2.2.2.2.1) := by
  unfold transactionProvisional
  rw [selected]
  rfl

/-- The transaction's creation branch is the exact EVM creation call. -/
theorem transaction_creation_result (accounts : AccountMap) (baseFee : Nat)
    (header genesis : BlockHeader) (blocks : ProcessedBlocks) (tx : Transaction) (sender : Address)
    (selected : tx.base.recipient = none) :
    transactionProvisional accounts baseFee header genesis blocks tx sender =
      let result := (transactionCreation accounts baseFee header genesis blocks tx sender).run
      (result.2.2.1, result.2.2.2.1, result.2.2.2.2.1, result.2.2.2.2.2.1) := by
  unfold transactionProvisional
  rw [selected]
  rfl

end Rollup.EVM
