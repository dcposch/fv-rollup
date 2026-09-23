import semantics.TransactionFees
import proofs.BoundaryCredit

open Ethereum Ethereum.EVM Reasoning.Theory

namespace Rollup.EVM

/-- A funded checkpoint debit has no modular underflow or multiplication overflow. -/
theorem checkpoint_balance (account : Account) (gasLimit price blobFee : UInt256)
    (funds : gasLimit.toNat * price.toNat + blobFee.toNat ≤ account.balance.toNat) :
    (account.balance - gasLimit * price - blobFee).toNat +
      gasLimit.toNat * price.toNat + blobFee.toNat = account.balance.toNat := by
  have product : gasLimit.toNat * price.toNat < UInt256.size := by
    have bound := account.balance.val.isLt
    change account.balance.toNat < UInt256.size at bound
    omega
  have paid := umul_toNat gasLimit price product
  have gasFunds : (gasLimit * price).toNat ≤ account.balance.toNat := by omega
  have first : (account.balance - gasLimit * price).toNat =
      account.balance.toNat - (gasLimit * price).toNat := usub_toNat gasFunds
  have blobFunds : blobFee.toNat ≤ (account.balance - gasLimit * price).toNat := by omega
  have second : (account.balance - gasLimit * price - blobFee).toNat =
      (account.balance - gasLimit * price).toNat - blobFee.toNat := usub_toNat blobFunds
  rw [second, first, paid]
  omega

/-- The checkpoint removes exactly the prepaid fees from total account balances. -/
theorem checkpoint_world (accounts : AccountMap) (sender : Address) (account : Account)
    (gasLimit price blobFee : UInt256) (found : accounts.find? sender = some account)
    (funds : gasLimit.toNat * price.toNat + blobFee.toNat ≤ account.balance.toNat) :
    worldEth (transactionCheckpoint accounts sender gasLimit price blobFee) +
      gasLimit.toNat * price.toNat + blobFee.toNat = worldEth accounts := by
  have balance := checkpoint_balance account gasLimit price blobFee funds
  have old : ethLedger accounts sender = account.balance.toNat := by
    simp [ethLedger, Batteries.RBMap.findD, found]
  simp only [transactionCheckpoint, found, Option.get!_some]
  have total := worldEth_insert accounts sender
    { account with balance := account.balance - gasLimit * price - blobFee
                   nonce := account.nonce + ⟨1⟩ }
  simp only [old] at total
  omega

/-- The sender fee debit preserves code and both storage maps. -/
theorem checkpoint_storage (accounts : AccountMap) (sender self : Address) (account : Account)
    (gasLimit price blobFee : UInt256) (found : accounts.find? sender = some account) :
    CodeStorageFrame self accounts (transactionCheckpoint accounts sender gasLimit price blobFee) := by
  simp only [transactionCheckpoint, found, Option.get!_some]
  apply accountStaticStateEq_of_storage_code
  · apply accountStorageStateEq_insert_preserve <;> simp [Batteries.RBMap.findD, found]
  · apply accountCodeStateEq_insert_preserve
    simp [Batteries.RBMap.findD, found]

/-- An external sender pays transaction fees without debiting the rollup. -/
theorem checkpoint_refines (accounts : AccountMap) (sender self : Address) (account : Account)
    (gasLimit price blobFee : UInt256) (keys : AccessScope)
    (found : accounts.find? sender = some account) (foreign : self ≠ sender)
    (funds : gasLimit.toNat * price.toNat + blobFee.toNat ≤ account.balance.toNat)
    (ready : BoundaryReady self accounts keys) (safe : Safe (boundaryModel self accounts keys)) :
    BoundaryRefines self keys accounts (transactionCheckpoint accounts sender gasLimit price blobFee) := by
  apply boundary_frame_refines ready safe
    (checkpoint_storage accounts sender self account gasLimit price blobFee found)
  constructor
  · have total := checkpoint_world accounts sender account gasLimit price blobFee found funds
    omega
  · simp only [transactionCheckpoint, found, Option.get!_some, ethLedger_insert,
      Function.update_of_ne foreign, le_refl]

/-- Refund and beneficiary credits preserve the boundary under their combined world bound. -/
theorem transaction_fee_credits_refine (accounts : AccountMap) (sender beneficiary self : Address)
    (refund fee : UInt256) (keys : AccessScope)
    (ready : BoundaryReady self accounts keys) (safe : Safe (boundaryModel self accounts keys))
    (bounded : worldEth accounts + refund.toNat + fee.toNat < wordLimit) :
    BoundaryRefines self keys accounts (transactionFeeCredits accounts sender beneficiary refund fee) := by
  have firstBound : worldEth accounts + refund.toNat < wordLimit := by omega
  have first := boundary_credit_refines self sender accounts refund keys ready safe firstBound
  have ownerBound : ethLedger accounts sender + refund.toNat < UInt256.size := by
    have part := balance_le_total (ethLedger accounts) sender
    change worldEth accounts + refund.toNat < UInt256.size at firstBound
    change ethLedger accounts sender ≤ worldEth accounts at part
    omega
  unfold transactionFeeCredits
  split
  · apply boundary_refines_trans first
    apply boundary_credit_refines self beneficiary _ fee keys first.1 first.2.1
    rw [increase_balance_world accounts sender refund ownerBound]
    exact bounded
  · exact first

/-- Refund and priority fees fit within the prepaid gas payment. -/
theorem gas_payment_credits_bound (limit returned price priority : Nat)
    (gasBound : returned ≤ limit) (priceBound : priority ≤ price) :
    returned * price + (limit - returned) * priority ≤ limit * price := by
  have part := Nat.mul_le_mul_left (limit - returned) priceBound
  have split : returned + (limit - returned) = limit := Nat.add_sub_of_le gasBound
  calc
    returned * price + (limit - returned) * priority ≤
        returned * price + (limit - returned) * price := Nat.add_le_add_left part _
    _ = (returned + (limit - returned)) * price := (Nat.add_mul _ _ _).symm
    _ = limit * price := by rw [split]

end Rollup.EVM
