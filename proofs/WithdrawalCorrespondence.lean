import proofs.WithdrawalBytecodeClassification
import proofs.WithdrawalCheckCorrespondence

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Rollup.EVM

/-- Lock acquisition changes only the account map. -/
theorem withdrawal_locked_state (evm : Ethereum.State) :
    withdrawalLockedState evm =
      { evm with accountMap := sstoreAccountMap evm.executionEnv.codeOwner evm.accountMap ⟨6⟩ ⟨1⟩ } := by
  unfold withdrawalLockedState Solm.EVM.storageStore sstoreAccountMap Ethereum.State.lookupAccount
  cases evm.accountMap.find? evm.executionEnv.codeOwner <;> rfl

/-- Equivalent account maps have the same saved withdrawal credit. -/
theorem withdrawal_input_credit_equiv {σ τ : AccountMap} (I : ExecutionEnv)
    (maps : accountMapEquiv σ τ) : withdrawalInputCredit σ I = withdrawalInputCredit τ I :=
  accountMapEquiv_storage_findD
    (accountMapEquiv_sstoreAccountMap I.codeOwner ⟨6⟩ ⟨1⟩ maps) I.codeOwner (withdrawalClaimSlot I) ⟨0⟩

/-- The final debit and unlock preserve equivalent account maps. -/
theorem withdrawal_output_accounts_equiv {σ τ after₁ after₂ : AccountMap} (I : ExecutionEnv)
    (beforeMaps : accountMapEquiv σ τ) (afterMaps : accountMapEquiv after₁ after₂) :
    accountMapEquiv (withdrawalOutputAccounts σ after₁ I) (withdrawalOutputAccounts τ after₂ I) := by
  unfold withdrawalOutputAccounts
  rw [withdrawal_input_credit_equiv I beforeMaps]
  exact accountMapEquiv_sstoreAccountMap I.codeOwner ⟨6⟩ ⟨0⟩
    (accountMapEquiv_sstoreAccountMap I.codeOwner _ _ afterMaps)

/-- Source and bytecode debit the same saved credit after the same call result. -/
theorem withdrawal_accounts_correspondence (before after : Ethereum.State) (owner : Address) (amount : Nat)
    (ownerBinding : UInt256.ofNat owner.val = calldataWord before.executionEnv.calldata 4)
    (amountBinding : amount = (calldataWord before.executionEnv.calldata 36).toNat)
    (environment : after.executionEnv = before.executionEnv)
    (covered : amount ≤ withdrawalCredit before owner) :
    (withdrawalFinalState before after owner amount).accountMap =
      withdrawalOutputAccounts before.accountMap after.accountMap before.executionEnv := by
  have credit : withdrawalCredit before owner =
      (withdrawalInputCredit before.accountMap before.executionEnv).toNat :=
    withdrawal_credit_correspondence before owner ownerBinding
  have word : UInt256.ofNat (withdrawalCredit before owner - amount) =
      UInt256.sub (withdrawalInputCredit before.accountMap before.executionEnv)
        (calldataWord before.executionEnv.calldata 36) := by
    apply u256_inj
    have bound : withdrawalCredit before owner - amount < UInt256.size := by
      rw [credit]
      exact lt_of_le_of_lt (Nat.sub_le _ _) (withdrawalInputCredit before.accountMap before.executionEnv).val.isLt
    rw [ulit_toNat' _ bound, usub_toNat (by rw [← amountBinding, ← credit]; exact covered),
      credit, amountBinding]
  simp only [withdrawalFinalState, withdrawalDebitedState, storageStore_accountMap,
    environment, withdrawal_claim_slot_binding ownerBinding, word, withdrawalOutputAccounts]

end Rollup.EVM
