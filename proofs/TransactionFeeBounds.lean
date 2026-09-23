import proofs.TransactionFees
import proofs.TransactionGas

open Ethereum Ethereum.EVM Reasoning.Theory

namespace Rollup.EVM

/-- Unsigned word minimum agrees with natural-number minimum. -/
theorem word_min_toNat (first second : UInt256) :
    (min first second).toNat = min first.toNat second.toNat := by
  change (if first.toNat ≤ second.toNat then first else second).toNat = _
  split
  · rename_i ordered
    exact (Nat.min_eq_left ordered).symm
  · rename_i unordered
    exact (Nat.min_eq_right (Nat.le_of_not_ge unordered)).symm

/-- The actual word refund calculation agrees with the one-fifth natural-number cap. -/
theorem refund_word_exact (limit remaining refund : UInt256)
    (bounded : remaining.toNat ≤ limit.toNat) :
    (remaining + min ((limit - remaining) / ⟨5⟩) refund).toNat =
      remaining.toNat + min ((limit.toNat - remaining.toNat) / 5) refund.toNat := by
  have difference : (limit - remaining).toNat = limit.toNat - remaining.toNat := usub_toNat bounded
  have division : ((limit - remaining) / (⟨5⟩ : UInt256)).toNat =
      (limit.toNat - remaining.toNat) / 5 := by
    have result := udiv_toNat (limit - remaining) ⟨5⟩
    change ((limit - remaining) / (⟨5⟩ : UInt256)).toNat = (limit - remaining).toNat / 5 at result
    rwa [difference] at result
  rw [uadd_toNat, word_min_toNat, division]
  apply Nat.mod_eq_of_lt
  have bound := refund_gas_bound limit.toNat remaining.toNat refund.toNat bounded
  exact bound.trans_lt limit.val.isLt

/-- The actual refund arithmetic cannot return more than the transaction gas limit. -/
theorem refund_word_bound (limit remaining refund : UInt256)
    (bounded : remaining.toNat ≤ limit.toNat) :
    (remaining + min ((limit - remaining) / ⟨5⟩) refund).toNat ≤ limit.toNat := by
  rw [refund_word_exact limit remaining refund bounded]
  exact refund_gas_bound limit.toNat remaining.toNat refund.toNat bounded

/-- Word refund and priority payments fit within prepaid gas, without overflow. -/
theorem fee_word_credits_bound (limit returned price priority : UInt256)
    (gasBound : returned.toNat ≤ limit.toNat) (priceBound : priority.toNat ≤ price.toNat)
    (prepaid : limit.toNat * price.toNat < UInt256.size) :
    (returned * price).toNat + ((limit - returned) * priority).toNat ≤
      limit.toNat * price.toNat := by
  have difference : (limit - returned).toNat = limit.toNat - returned.toNat := usub_toNat gasBound
  have sumBound := gas_payment_credits_bound limit.toNat returned.toNat price.toNat priority.toNat
    gasBound priceBound
  have refundBound : returned.toNat * price.toNat < UInt256.size := by omega
  have feeBound : (limit - returned).toNat * priority.toNat < UInt256.size := by
    rw [difference]
    omega
  rw [umul_toNat returned price refundBound, umul_toNat (limit - returned) priority feeBound, difference]
  exact sumBound

/-- Prepaid fees bound final credits after an execution that does not increase total ETH. -/
theorem prepaid_fee_credits_refine (before provisional : AccountMap)
    (sender beneficiary self : Address) (account : Account) (limit price priority blobFee returned : UInt256)
    (keys : AccessScope) (found : before.find? sender = some account)
    (funds : limit.toNat * price.toNat + blobFee.toNat ≤ account.balance.toNat)
    (world : worldEth before < wordLimit)
    (execution : worldEth provisional ≤ worldEth (transactionCheckpoint before sender limit price blobFee))
    (gasBound : returned.toNat ≤ limit.toNat) (priceBound : priority.toNat ≤ price.toNat)
    (ready : BoundaryReady self provisional keys) (safe : Safe (boundaryModel self provisional keys)) :
    BoundaryRefines self keys provisional
      (transactionFeeCredits provisional sender beneficiary (returned * price) ((limit - returned) * priority)) := by
  have prepaid : limit.toNat * price.toNat < UInt256.size := by
    have bound := account.balance.val.isLt
    change account.balance.toNat < UInt256.size at bound
    omega
  have credits := fee_word_credits_bound limit returned price priority gasBound priceBound prepaid
  have checkpoint := checkpoint_world before sender account limit price blobFee found funds
  apply transaction_fee_credits_refine provisional sender beneficiary self _ _ keys ready safe
  omega

end Rollup.EVM
