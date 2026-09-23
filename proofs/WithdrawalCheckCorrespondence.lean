import proofs.WithdrawalSource
import proofs.WithdrawalBytecodeChecks

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Rollup.EVM

/-- Source and bytecode use the same claim slot for a bound owner. -/
theorem withdrawal_claim_slot_binding {I : ExecutionEnv} {owner : Address}
    (binding : UInt256.ofNat owner.val = calldataWord I.calldata 4) :
    keySlot (.claims owner) = withdrawalClaimSlot I := by
  simp only [keySlot, mapSlot, keyValueToWord_address, withdrawalClaimSlot, solcMappingSlot, binding]

/-- Source and bytecode read the same credit after setting the lock. -/
theorem withdrawal_credit_correspondence (evm : Ethereum.State) (owner : Address)
    (binding : UInt256.ofNat owner.val = calldataWord evm.executionEnv.calldata 4) :
    withdrawalCredit evm owner =
      (withdrawalClaimWord (sstoreAccountMap evm.executionEnv.codeOwner evm.accountMap ⟨6⟩ ⟨1⟩)
        evm.executionEnv).toNat := by
  have read_map (state : Ethereum.State) (I : ExecutionEnv) (slot : UInt256) :
      readWord state I.codeOwner slot = solcSlotWord state.accountMap I slot := rfl
  simp only [withdrawalCredit, withdrawalLockedState, read_map, storageStore_accountMap,
    withdrawal_claim_slot_binding binding, withdrawalClaimWord]

/-- Bytecode prelude checks imply the matching source checks. -/
theorem withdrawal_checks_to_source (evm : Ethereum.State) (owner : Address) (amount : Nat)
    (ownerBinding : UInt256.ofNat owner.val = calldataWord evm.executionEnv.calldata 4)
    (amountBinding : amount = (calldataWord evm.executionEnv.calldata 36).toNat)
    (checks : WithdrawalBytecodeChecks evm.accountMap evm.executionEnv) :
    WithdrawalExecutionChecks evm owner amount := by
  refine ⟨checks.nonpayable, checks.unlocked, ?_, ?_⟩
  · intro zero
    exact checks.positive (uint256_toNat_eq_zero (amountBinding.symm.trans zero))
  · rw [amountBinding, withdrawal_credit_correspondence evm owner ownerBinding]
    exact checks.covered

/-- Source prelude checks imply the bytecode checks after valid ABI decoding. -/
theorem withdrawal_checks_to_bytecode (evm : Ethereum.State) (owner : Address) (amount : Nat)
    (ownerBinding : UInt256.ofNat owner.val = calldataWord evm.executionEnv.calldata 4)
    (amountBinding : amount = (calldataWord evm.executionEnv.calldata 36).toNat)
    (length : 68 ≤ evm.executionEnv.calldata.size)
    (signedBound : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (canonical : (calldataWord evm.executionEnv.calldata 4).toNat < _root_.EVM.addressModulus)
    (checks : WithdrawalExecutionChecks evm owner amount) :
    WithdrawalBytecodeChecks evm.accountMap evm.executionEnv := by
  refine ⟨checks.nonpayable, length, signedBound, canonical, checks.unlocked, ?_, ?_⟩
  · intro zero
    apply checks.positive
    rw [amountBinding, zero]
    rfl
  · rw [← amountBinding, ← withdrawal_credit_correspondence evm owner ownerBinding]
    exact checks.covered

private theorem checks_transfer {σ τ : AccountMap} (I : ExecutionEnv)
    (maps : accountMapEquiv σ τ) (checks : WithdrawalBytecodeChecks σ I) :
    WithdrawalBytecodeChecks τ I := by
  have lock := accountMapEquiv_storage_findD maps I.codeOwner ⟨6⟩ ⟨0⟩
  have claim : solcSlotWord (sstoreAccountMap I.codeOwner σ ⟨6⟩ ⟨1⟩) I (withdrawalClaimSlot I) =
      solcSlotWord (sstoreAccountMap I.codeOwner τ ⟨6⟩ ⟨1⟩) I (withdrawalClaimSlot I) :=
    accountMapEquiv_storage_findD (accountMapEquiv_sstoreAccountMap I.codeOwner ⟨6⟩ ⟨1⟩ maps)
      I.codeOwner (withdrawalClaimSlot I) ⟨0⟩
  refine ⟨checks.nonpayable, checks.length, checks.signedBound, checks.canonical, ?_, checks.positive, ?_⟩
  · exact lock.symm.trans checks.unlocked
  · change (calldataWord I.calldata 36).toNat ≤
      (solcSlotWord (sstoreAccountMap I.codeOwner τ ⟨6⟩ ⟨1⟩) I (withdrawalClaimSlot I)).toNat
    rw [← claim]
    exact checks.covered

/-- Equivalent account maps have the same withdrawal prelude checks. -/
theorem withdrawal_checks_equiv {σ τ : AccountMap} (I : ExecutionEnv)
    (maps : accountMapEquiv σ τ) :
    WithdrawalBytecodeChecks σ I ↔ WithdrawalBytecodeChecks τ I :=
  ⟨checks_transfer I maps, checks_transfer I maps.symm⟩

end Rollup.EVM
