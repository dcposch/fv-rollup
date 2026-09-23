import proofs.WithdrawalPrefixCredit

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Rollup.EVM

/-- A prefix to the payment passes the checks and sets the lock. -/
theorem withdrawal_prefix_checks {I : ExecutionEnv} {target child : Ethereum.State}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (four : 4 ≤ I.calldata.size) (bounded : I.calldata.size < UInt256.size)
    (dispatched : PCR runtimeBytecode I target child ⟨284⟩ [⟨0xbb3ef682⟩]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ)) :
    WithdrawalBytecodeChecks σ I ∧
      PCR runtimeBytecode I target child ⟨908⟩
        [withdrawalClaimWord (sstoreAccountMap I.codeOwner σ ⟨6⟩ ⟨1⟩) I,
          calldataWord I.calldata 36, calldataWord I.calldata 4, ⟨226⟩, ⟨0xbb3ef682⟩]
        (twoWordHashMem (calldataWord I.calldata 4) ⟨5⟩ solcFreePtrMem) (UInt256.ofNat 3)
        ByteArray.empty (cA, sstoreAccountMap I.codeOwner σ ⟨6⟩ ⟨1⟩) := by
  obtain ⟨nonpayable, length, signedBound, canonical, entry⟩ :=
    withdrawal_prefix_entry four bounded dispatched
  have slot := runtime_run entry with [jumpdest, push1 ⟨6⟩]
  have loaded := slot.sload (by decide +kernel) (by evm_ov)
  have unlocked : solcSlotWord σ I ⟨6⟩ = ⟨0⟩ := by
    by_contra locked
    have rejected := runtime_run loaded with [iszero, push2 ⟨855⟩,
      jumpiNT (isZero_eq_zero_of_ne locked), push0, dup1]
    exact rejected.halt (arg := none) (by decide +kernel) (Or.inr (Or.inr (Or.inl rfl)))
  change PCR runtimeBytecode I target child _
    (solcSlotWord σ I ⟨6⟩ :: _) _ _ _ _ at loaded
  rw [unlocked] at loaded
  have acquired := runtime_run loaded with [iszero, push2 ⟨855⟩,
    jumpiT (by decide) (jumpScan_valid runtimeBytecode 855 880 (by decide +kernel)),
    jumpdest, push1 ⟨1⟩, push1 ⟨6⟩]
  have writable := acquired.sstore_permission (by decide +kernel)
  have entered := acquired.sstore writable (by decide +kernel) (by evm_ov)
  have guard := runtime_run entered with [push0, dup2, swap1, sub, push2 ⟨872⟩]
  have positive : calldataWord I.calldata 36 ≠ ⟨0⟩ := by
    intro zero
    rw [zero] at guard
    have rejected := runtime_run guard with [jumpiNT (by decide), push0, dup1]
    exact rejected.halt (arg := none) (by decide +kernel) (Or.inr (Or.inr (Or.inl rfl)))
  have checkedAmount := runtime_run guard with [jumpiT (u256_zero_sub_ne_zero positive)
    (jumpScan_valid runtimeBytecode 872 900 (by decide +kernel))]
  have credit := withdrawal_prefix_credit_load [⟨226⟩, ⟨0xbb3ef682⟩] (by decide)
    canonical solcFreePtrMem_size checkedAmount
  have guard := runtime_run credit with [dup1, dup3, gt, iszero, push2 ⟨908⟩]
  have covered : (calldataWord I.calldata 36).toNat ≤
      (withdrawalClaimWord (sstoreAccountMap I.codeOwner σ ⟨6⟩ ⟨1⟩) I).toNat := by
    by_contra tooLarge
    have greater := ugt_one (by omega :
      (withdrawalClaimWord (sstoreAccountMap I.codeOwner σ ⟨6⟩ ⟨1⟩) I).toNat <
        (calldataWord I.calldata 36).toNat)
    have rejected := runtime_run guard with [jumpiNT (by rw [greater]; decide), push0, dup1]
    exact rejected.halt (arg := none) (by decide +kernel) (Or.inr (Or.inr (Or.inl rfl)))
  exact ⟨⟨nonpayable, length, signedBound, canonical, unlocked, positive, covered⟩,
    runtime_run guard with [jumpiT (by rw [ugt_zero covered]; decide)
      (jumpScan_valid runtimeBytecode 908 940 (by decide +kernel))]⟩

end Rollup.EVM
