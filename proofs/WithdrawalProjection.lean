import proofs.WithdrawalBalances
import proofs.WithdrawalStorageEffects

open Solm Ethereum Reasoning.Theory

namespace Rollup.EVM

/-- Source storage writes preserve the complete ETH ledger. -/
theorem source_store_ethLedger (evm : Ethereum.State) (self : Address) (slot value : UInt256) :
    ethLedger (Solm.EVM.storageStore evm self slot value).accountMap = ethLedger evm.accountMap := by
  have view (state : Ethereum.State) (owner : Address) :
      ethLedger state.accountMap owner =
        (((state.lookupAccount owner).map (fun account : Account => account.balance)).getD (⟨0⟩ : UInt256)).toNat := by
    rw [ethLedger_lookup]
    simp only [Ethereum.State.lookupAccount]
    cases state.accountMap.find? owner <;> rfl
  funext owner
  rw [view, view, all_balances_store]

/-- The lock slot is absent from the accounting projection. -/
theorem withdrawal_lock_projection (before : Ethereum.State) (keys : AccessScope)
    (code : OwnCode before) (ready : StorageReady before before.executionEnv.codeOwner keys) :
    project (withdrawalLockedState before) before.executionEnv.codeOwner keys =
      project before before.executionEnv.codeOwner keys := by
  obtain ⟨account, found, _⟩ := pinned_account_present (ownCode_default code)
  have fixed (i : Fin 7) : StorageKey.fixed i ∈ keys := ready.1 (by simp [fixedKeys])
  have reads (key : StorageKey) (tracked : key ∈ keys) (different : key ≠ .fixed 6) :
      readWord (withdrawalLockedState before) before.executionEnv.codeOwner (keySlot key) =
        readWord before before.executionEnv.codeOwner (keySlot key) := by
    have slot := read_store_key found ready.2.1 tracked (fixed 6) ⟨1⟩
    simpa only [different, if_false] using slot
  have pending : pendingLedger (withdrawalLockedState before) before.executionEnv.codeOwner keys =
      pendingLedger before before.executionEnv.codeOwner keys := by
    funext owner
    by_cases tracked : StorageKey.pending owner ∈ keys
    · simp only [pendingLedger, tracked, if_true, reads _ tracked (by simp)]
    · simp only [pendingLedger, tracked, if_false]
  have claims : claimLedger (withdrawalLockedState before) before.executionEnv.codeOwner keys =
      claimLedger before before.executionEnv.codeOwner keys := by
    funext owner
    by_cases tracked : StorageKey.claims owner ∈ keys
    · simp only [claimLedger, tracked, if_true, reads _ tracked (by simp)]
    · simp only [claimLedger, tracked, if_false]
  have seq : readWord (withdrawalLockedState before) before.executionEnv.codeOwner ⟨0⟩ =
      readWord before before.executionEnv.codeOwner ⟨0⟩ := by
    simpa using reads (.fixed 0) (fixed 0) (by decide)
  have root : readWord (withdrawalLockedState before) before.executionEnv.codeOwner ⟨1⟩ =
      readWord before before.executionEnv.codeOwner ⟨1⟩ := by
    simpa using reads (.fixed 1) (fixed 1) (by decide)
  have number : readWord (withdrawalLockedState before) before.executionEnv.codeOwner ⟨2⟩ =
      readWord before before.executionEnv.codeOwner ⟨2⟩ := by
    simpa using reads (.fixed 2) (fixed 2) (by decide)
  have backing : readWord (withdrawalLockedState before) before.executionEnv.codeOwner ⟨3⟩ =
      readWord before before.executionEnv.codeOwner ⟨3⟩ := by
    simpa using reads (.fixed 3) (fixed 3) (by decide)
  have eth : (project (withdrawalLockedState before) before.executionEnv.codeOwner keys).eth =
      (project before before.executionEnv.codeOwner keys).eth := by
    rw [project_ethLedger, project_ethLedger]
    exact congrFun (source_store_ethLedger before before.executionEnv.codeOwner ⟨6⟩ ⟨1⟩) _
  simpa only [project, pending, claims, seq, root, number, backing,
    Rollup.State.mk.injEq, true_and, and_true] using eth

theorem withdrawal_credit_model (before : Ethereum.State) (owner : Address) (keys : AccessScope)
    (code : OwnCode before) (ready : StorageReady before before.executionEnv.codeOwner keys)
    (tracked : StorageKey.claims owner ∈ keys) :
    withdrawalCredit before owner = (project before before.executionEnv.codeOwner keys).claims owner := by
  rw [← withdrawal_lock_projection before keys code ready]
  simp only [project, claimLedger, tracked, if_true, withdrawalCredit]

/-- The final writes debit one credit and retain the callback's ETH balance. -/
theorem withdrawal_final_projection {before after : Ethereum.State} {owner : Address}
    {amount : Nat} {output : ByteArray} (keys : AccessScope)
    (code : OwnCode before) (ready : StorageReady before before.executionEnv.codeOwner keys)
    (tracked : StorageKey.claims owner ∈ keys)
    (unlocked : readWord before before.executionEnv.codeOwner ⟨6⟩ = ⟨0⟩)
    (call : callViaEVM (withdrawalLockedState before) owner amount ByteArray.empty (true, after, output)) :
    project (withdrawalFinalState before after owner amount) before.executionEnv.codeOwner keys =
      { project before before.executionEnv.codeOwner keys with
        claims := debit (project before before.executionEnv.codeOwner keys).claims owner amount
        eth := (project after before.executionEnv.codeOwner keys).eth } := by
  have slots := withdrawal_final_storage_values keys code ready tracked unlocked call
  have credit := withdrawal_credit_model before owner keys code ready tracked
  have creditBound : withdrawalCredit before owner - amount < wordLimit :=
    lt_of_le_of_lt (Nat.sub_le _ _) (readWord (withdrawalLockedState before)
      before.executionEnv.codeOwner (keySlot (.claims owner))).val.isLt
  have pending : pendingLedger (withdrawalFinalState before after owner amount) before.executionEnv.codeOwner keys =
      pendingLedger before before.executionEnv.codeOwner keys := by
    funext other
    by_cases member : StorageKey.pending other ∈ keys
    · have slot := slots (.pending other) member
      simp only [reduceCtorEq, if_false] at slot
      simp only [pendingLedger, member, if_true, slot]
    · simp only [pendingLedger, member, if_false]
  have claims : claimLedger (withdrawalFinalState before after owner amount) before.executionEnv.codeOwner keys =
      debit (claimLedger before before.executionEnv.codeOwner keys) owner amount := by
    funext other
    by_cases same : other = owner
    · subst other
      have slot := slots (.claims owner) tracked
      simp only [if_true] at slot
      simp only [claimLedger, tracked, if_true, debit, Function.update_self, slot]
      rw [ulit_toNat' _ creditBound, credit]
      simp only [project, claimLedger, tracked, if_true]
    · by_cases member : StorageKey.claims other ∈ keys
      · have slot := slots (.claims other) member
        simp only [StorageKey.claims.injEq, same, if_false] at slot
        simp only [claimLedger, member, if_true, debit, Function.update_of_ne same, slot]
      · simp only [claimLedger, member, if_false, debit, Function.update_of_ne same]
  have fixed (i : Fin 7) : StorageKey.fixed i ∈ keys := ready.1 (by simp [fixedKeys])
  have seq : readWord (withdrawalFinalState before after owner amount) before.executionEnv.codeOwner ⟨0⟩ =
      readWord before before.executionEnv.codeOwner ⟨0⟩ := by
    simpa using slots (.fixed 0) (fixed 0)
  have root : readWord (withdrawalFinalState before after owner amount) before.executionEnv.codeOwner ⟨1⟩ =
      readWord before before.executionEnv.codeOwner ⟨1⟩ := by
    simpa using slots (.fixed 1) (fixed 1)
  have number : readWord (withdrawalFinalState before after owner amount) before.executionEnv.codeOwner ⟨2⟩ =
      readWord before before.executionEnv.codeOwner ⟨2⟩ := by
    simpa using slots (.fixed 2) (fixed 2)
  have backing : readWord (withdrawalFinalState before after owner amount) before.executionEnv.codeOwner ⟨3⟩ =
      readWord before before.executionEnv.codeOwner ⟨3⟩ := by
    simpa using slots (.fixed 3) (fixed 3)
  have environment : after.executionEnv = before.executionEnv := by
    simpa only [withdrawalLockedState, storageStore_executionEnv] using source_callback_environment call
  have eth : (project (withdrawalFinalState before after owner amount) before.executionEnv.codeOwner keys).eth =
      (project after before.executionEnv.codeOwner keys).eth := by
    rw [project_ethLedger, project_ethLedger]
    simp only [withdrawalFinalState, withdrawalDebitedState, environment,
      source_store_ethLedger]
  simpa only [project, pending, claims, seq, root, number, backing,
    Rollup.State.mk.injEq, true_and, and_true] using eth

end Rollup.EVM
