import semantics.TransactionCalls
import proofs.TransactionFeeBounds
import semantics.TransactionExecution

open Ethereum Ethereum.EVM Reasoning.Theory

namespace Rollup.EVM

/-- A funded legacy gas price covers its priority component. -/
theorem legacy_priority_bound (price : UInt256) (baseFee : Nat) (covered : baseFee ≤ price.toNat) :
    (price - UInt256.ofNat baseFee).toNat ≤ price.toNat := by
  have baseWord := UInt256.toNat_ofNat_of_lt (covered.trans_lt price.val.isLt)
  have paid : (UInt256.ofNat baseFee).toNat ≤ price.toNat := by rwa [baseWord]
  have difference : (price - UInt256.ofNat baseFee).toNat =
      price.toNat - (UInt256.ofNat baseFee).toNat := usub_toNat paid
  rw [difference]
  exact Nat.sub_le _ _

/-- A valid fee cap prevents overflow in the dynamic effective gas price. -/
theorem dynamic_priority_bound (cap priority : UInt256) (baseFee : Nat) (covered : baseFee ≤ cap.toNat) :
    (min priority (cap - UInt256.ofNat baseFee)).toNat ≤
      (min priority (cap - UInt256.ofNat baseFee) + UInt256.ofNat baseFee).toNat := by
  have baseWord := UInt256.toNat_ofNat_of_lt (covered.trans_lt cap.val.isLt)
  have paid : (UInt256.ofNat baseFee).toNat ≤ cap.toNat := by rwa [baseWord]
  have difference : (cap - UInt256.ofNat baseFee).toNat = cap.toNat - baseFee := by
    have sub : (cap - UInt256.ofNat baseFee).toNat = cap.toNat - (UInt256.ofNat baseFee).toNat := usub_toNat paid
    rwa [baseWord] at sub
  have priorityBound : (min priority (cap - UInt256.ofNat baseFee)).toNat + baseFee ≤ cap.toNat := by
    rw [word_min_toNat, difference]
    have part := Nat.min_le_right priority.toNat (cap.toNat - baseFee)
    omega
  rw [uadd_toNat, baseWord, Nat.mod_eq_of_lt (priorityBound.trans_lt cap.val.isLt)]
  exact Nat.le_add_right _ _

/-- Every supported transaction type has priority price at most its effective gas price. -/
theorem transaction_fee_price_bound (tx : Transaction) (baseFee : Nat)
    (covered : baseFee ≤ (transactionFeeCap tx).toNat) :
    (transactionPriorityFee baseFee tx).toNat ≤ (transactionGasPrice baseFee tx).toNat := by
  cases tx with
  | legacy data => exact legacy_priority_bound data.gasPrice baseFee covered
  | access data => exact legacy_priority_bound data.gasPrice baseFee covered
  | dynamic data => exact dynamic_priority_bound data.maxFeePerGas data.maxPriorityFeePerGas baseFee covered
  | blob data => exact dynamic_priority_bound data.maxFeePerGas data.maxPriorityFeePerGas baseFee covered

/-- The transaction nonce bound prevents the checkpoint increment from wrapping to zero. -/
theorem checkpoint_nonce_nonzero (accounts : AccountMap) (sender : Address) (account : Account)
    (limit price blobFee : UInt256) (found : accounts.find? sender = some account)
    (bounded : account.nonce.toNat < 2 ^ 64 - 1) :
    ((transactionCheckpoint accounts sender limit price blobFee).findD sender default).nonce ≠ ⟨0⟩ := by
  simp only [transactionCheckpoint, found, Option.get!_some, Batteries.RBMap.findD,
    accountMap_find_insert_self, Option.getD_some]
  intro zero
  have equation := congrArg UInt256.toNat zero
  rw [uadd_toNat] at equation
  have small : account.nonce.toNat + 1 < UInt256.size := by
    change account.nonce.toNat + 1 < 2 ^ 256
    omega
  simp only [UInt256.zero_toNat] at equation
  change (account.nonce.toNat + 1) % UInt256.size = 0 at equation
  rw [Nat.mod_eq_of_lt small] at equation
  omega

/-- Upfront funding leaves enough ETH for the transaction value after fee payment. -/
theorem checkpoint_value_funded (accounts : AccountMap) (sender : Address) (account : Account)
    (limit price blobFee value : UInt256) (found : accounts.find? sender = some account)
    (funds : limit.toNat * price.toNat + blobFee.toNat + value.toNat ≤ account.balance.toNat) :
    value.toNat ≤ ethLedger (transactionCheckpoint accounts sender limit price blobFee) sender := by
  have fees : limit.toNat * price.toNat + blobFee.toNat ≤ account.balance.toNat := by omega
  have balance := checkpoint_balance account limit price blobFee fees
  simp only [transactionCheckpoint, found, Option.get!_some, ethLedger_insert, Function.update_self]
  omega

end Rollup.EVM
