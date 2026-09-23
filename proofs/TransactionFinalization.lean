import semantics.TransactionExecution
import proofs.TransactionFeeBounds
import proofs.TransactionCleanup

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- The transaction helpers are a direct decomposition of the pinned EVM transaction function. -/
theorem transaction_execution_eq (accounts : AccountMap) (baseFee : Nat)
    (header genesis : BlockHeader) (blocks : ProcessedBlocks) (tx : Transaction) (sender : Address) :
    Υ accounts baseFee header genesis blocks tx sender =
      let result := transactionProvisional accounts baseFee header genesis blocks tx sender
      let returned := result.2.1 + min ((tx.base.gasLimit - result.2.1) / ⟨5⟩) result.2.2.1.refundBalance
      .ok (transactionFinalAccounts result.1 sender header.beneficiary tx.base.gasLimit result.2.1
          (transactionGasPrice baseFee tx) (transactionPriorityFee baseFee tx) result.2.2.1,
        result.2.2.1, result.2.2.2, tx.base.gasLimit - returned) := by
  unfold Υ transactionProvisional transactionFinalAccounts transactionFeeCredits transactionCleanup
    transactionCheckpoint transactionGasPrice transactionPriorityFee transactionInitialSubstate
  cases tx.base.recipient <;> rfl

/-- Finalization composes fee credits and cleanup once execution discharges its world and deletion conditions. -/
theorem transaction_finalization_refines (before provisional : AccountMap)
    (sender beneficiary self : Address) (account : Account) (limit price priority blobFee remaining : UInt256)
    (substate : Substate) (keys : AccessScope) (found : before.find? sender = some account)
    (funds : limit.toNat * price.toNat + blobFee.toNat ≤ account.balance.toNat)
    (world : worldEth before < wordLimit)
    (execution : worldEth provisional ≤ worldEth (transactionCheckpoint before sender limit price blobFee))
    (gasBound : remaining.toNat ≤ limit.toNat) (priceBound : priority.toNat ≤ price.toNat)
    (absent : self ∉ substate.selfDestructSet)
    (ready : BoundaryReady self provisional keys) (safe : Safe (boundaryModel self provisional keys)) :
    BoundaryRefines self keys provisional
      (transactionFinalAccounts provisional sender beneficiary limit remaining price priority substate) := by
  have bound := refund_word_bound limit remaining substate.refundBalance gasBound
  have fees := prepaid_fee_credits_refine before provisional sender beneficiary self account
    limit price priority blobFee _ keys found funds world execution bound priceBound ready safe
  have cleanup := transaction_cleanup_refines self _ substate keys absent fees.1 fees.2.1
  exact boundary_refines_trans fees cleanup

end Rollup.EVM
