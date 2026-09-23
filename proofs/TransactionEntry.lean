import semantics.TransactionExecution
import proofs.TransactionGas
import proofs.AddressOrder

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- A transaction starts with no pending account deletions. -/
theorem transaction_initial_deletions (header : BlockHeader) (tx : Transaction) (sender : Address) :
    (transactionInitialSubstate header tx sender).selfDestructSet = .empty := rfl

/-- Transaction message and creation execution cannot increase the supplied execution gas. -/
theorem transaction_provisional_gas_bound (accounts : AccountMap) (baseFee : Nat)
    (header genesis : BlockHeader) (blocks : ProcessedBlocks) (tx : Transaction) (sender : Address) :
    (transactionProvisional accounts baseFee header genesis blocks tx sender).2.1.toNat ≤
      (UInt256.ofNat (tx.base.gasLimit.toNat - intrinsicGas tx)).toNat := by
  unfold transactionProvisional
  dsimp only
  split
  · exact creation_gas_bound {
      blobs := tx.blobVersionedHashes
      created := .empty
      genesis := genesis
      blocks := blocks
      accounts := transactionCheckpoint accounts sender tx.base.gasLimit
        (transactionGasPrice baseFee tx) (.ofNat (calcBlobFee header tx))
      original := transactionCheckpoint accounts sender tx.base.gasLimit
        (transactionGasPrice baseFee tx) (.ofNat (calcBlobFee header tx))
      substate := transactionInitialSubstate header tx sender
      sender := sender
      origin := sender
      gas := .ofNat (tx.base.gasLimit.toNat - intrinsicGas tx)
      gasPrice := transactionGasPrice baseFee tx
      depth := 0
      salt := none
      header := header
      value := tx.base.value
      initCode := tx.base.data
      writable := true }
  · exact Theta_gas_le

/-- Provisional gas is bounded by the original transaction gas limit. -/
theorem transaction_remaining_gas_bound (accounts : AccountMap) (baseFee : Nat)
    (header genesis : BlockHeader) (blocks : ProcessedBlocks) (tx : Transaction) (sender : Address) :
    (transactionProvisional accounts baseFee header genesis blocks tx sender).2.1.toNat ≤
      tx.base.gasLimit.toNat := by
  have bound := transaction_provisional_gas_bound accounts baseFee header genesis blocks tx sender
  exact bound.trans ((Nat.mod_le _ _).trans (Nat.sub_le _ _))

end Rollup.EVM
