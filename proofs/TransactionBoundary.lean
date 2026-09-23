import proofs.TransactionProvisional
import proofs.TransactionPreconditions
import proofs.TransactionFinalization
import proofs.TransactionEntry

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- Transaction accounting is complete once execution excludes the rollup from pending deletion. -/
theorem transaction_boundary_of_no_deletion (accounts after : AccountMap) (baseFee : Nat)
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
    (absent : self ∉ (transactionProvisional accounts baseFee header genesis blocks tx sender).2.2.1.selfDestructSet)
    (executed : Υ accounts baseFee header genesis blocks tx sender = .ok (after, finalSubstate, accepted, gas)) :
    BoundaryRefines self keys accounts after := by
  have blobBound : calcBlobFee header tx < UInt256.size := by
    have bound := account.balance.val.isLt
    change account.balance.toNat < UInt256.size at bound
    omega
  have blobWord := UInt256.toNat_ofNat_of_lt blobBound
  have wordFunds : tx.base.gasLimit.toNat * (transactionGasPrice baseFee tx).toNat +
      (UInt256.ofNat (calcBlobFee header tx)).toNat + tx.base.value.toNat ≤ account.balance.toNat := by
    rwa [blobWord]
  have feeFunds : tx.base.gasLimit.toNat * (transactionGasPrice baseFee tx).toNat +
      (UInt256.ofNat (calcBlobFee header tx)).toNat ≤ account.balance.toNat := by omega
  have checkpoint := checkpoint_refines accounts sender self account tx.base.gasLimit
    (transactionGasPrice baseFee tx) (.ofNat (calcBlobFee header tx)) keys found foreign feeFunds ready safe
  have nonce := checkpoint_nonce_nonzero accounts sender account tx.base.gasLimit
    (transactionGasPrice baseFee tx) (.ofNat (calcBlobFee header tx)) found nonceBound
  have valueFunds := checkpoint_value_funded accounts sender account tx.base.gasLimit
    (transactionGasPrice baseFee tx) (.ofNat (calcBlobFee header tx)) tx.base.value found wordFunds
  have provisional := transaction_provisional_preserves accounts baseFee header genesis blocks tx sender self keys
    ordinary foreign bounded checkpoint.1 checkpoint.2.1 nonce valueFunds scope
  have finish := transaction_finalization_refines accounts
    (transactionProvisional accounts baseFee header genesis blocks tx sender).1
    sender header.beneficiary self account tx.base.gasLimit (transactionGasPrice baseFee tx)
    (transactionPriorityFee baseFee tx) (.ofNat (calcBlobFee header tx))
    (transactionProvisional accounts baseFee header genesis blocks tx sender).2.1
    (transactionProvisional accounts baseFee header genesis blocks tx sender).2.2.1 keys
    found feeFunds (BoundaryReady.world ready) provisional.2
    (transaction_remaining_gas_bound accounts baseFee header genesis blocks tx sender)
    (transaction_fee_price_bound tx baseFee priceBound) absent provisional.1.1 provisional.1.2.1
  have complete := boundary_refines_trans checkpoint (boundary_refines_trans provisional.1 finish)
  rw [transaction_execution_eq] at executed
  have same := congrArg (fun result => result.1) (Except.ok.inj executed)
  dsimp only at same
  rw [← same]
  exact complete

end Rollup.EVM
