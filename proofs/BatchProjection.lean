import proofs.BatchStorageEffects

open Solm Ethereum Reasoning.Theory

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Rollup.EVM

/-- The seven storage writes implement the model batch, including coincident owners. -/
theorem batch_projection (evm : Ethereum.State) (batch : Batch) (keys : AccessScope)
    (present : ∃ account, evm.lookupAccount evm.executionEnv.codeOwner = some account)
    (ready : StorageReady evm evm.executionEnv.codeOwner keys)
    (pendingKey : StorageKey.pending batch.depositOwner ∈ keys)
    (claimsKey : StorageKey.claims batch.withdrawalOwner ∈ keys)
    (numberBound : batch.number < wordLimit)
    (availableBound : batchAvailable evm batch < wordLimit)
    (creditBound : batchNextCredit evm batch < wordLimit) :
    project (batchExecutionState evm batch) evm.executionEnv.codeOwner keys =
      executeBatch (project evm evm.executionEnv.codeOwner keys) batch := by
  have slots := batch_storage evm batch keys present ready pendingKey claimsKey
  have reads := batch_read_values evm batch keys ready pendingKey claimsKey
  have depositBound : batchDepositCredit evm batch - batch.depositAmount < wordLimit :=
    lt_of_le_of_lt (Nat.sub_le _ _) (readWord (batchLockedState evm)
      evm.executionEnv.codeOwner (keySlot (.pending batch.depositOwner))).val.isLt
  have backingBound : batchAvailable evm batch - batch.withdrawalAmount < wordLimit :=
    lt_of_le_of_lt (Nat.sub_le _ _) availableBound
  have pending : pendingLedger (batchExecutionState evm batch) evm.executionEnv.codeOwner keys =
      debit (pendingLedger evm evm.executionEnv.codeOwner keys) batch.depositOwner batch.depositAmount := by
    funext owner
    by_cases same : owner = batch.depositOwner
    · subst owner
      have update := slots (.pending batch.depositOwner) pendingKey
      simp only [reduceCtorEq, if_false, if_true] at update
      simp only [pendingLedger, pendingKey, if_true, debit, Function.update_self, update]
      rw [ulit_toNat' _ depositBound, reads.1]
      simp only [project, pendingLedger, pendingKey, if_true]
    · by_cases tracked : StorageKey.pending owner ∈ keys
      · have update := slots (.pending owner) tracked
        simp only [reduceCtorEq, StorageKey.pending.injEq, same, if_false] at update
        simp [pendingLedger, tracked, debit, same, update]
      · simp [pendingLedger, tracked, debit, same]
  have claims : claimLedger (batchExecutionState evm batch) evm.executionEnv.codeOwner keys =
      credit (claimLedger evm evm.executionEnv.codeOwner keys) batch.withdrawalOwner batch.withdrawalAmount := by
    funext owner
    by_cases same : owner = batch.withdrawalOwner
    · subst owner
      have update := slots (.claims batch.withdrawalOwner) claimsKey
      simp only [reduceCtorEq, if_false, if_true] at update
      simp only [claimLedger, claimsKey, if_true, credit, Function.update_self, update]
      rw [ulit_toNat' _ creditBound, reads.2.2]
      simp only [project, claimLedger, claimsKey, if_true]
    · by_cases tracked : StorageKey.claims owner ∈ keys
      · have update := slots (.claims owner) tracked
        simp only [reduceCtorEq, StorageKey.claims.injEq, same, if_false] at update
        simp [claimLedger, tracked, credit, same, update]
      · simp [claimLedger, tracked, credit, same]
  have fixed (i : Fin 7) : StorageKey.fixed i ∈ keys := ready.1 (by simp [fixedKeys])
  have seq : readWord (batchExecutionState evm batch) evm.executionEnv.codeOwner ⟨0⟩ =
      readWord evm evm.executionEnv.codeOwner ⟨0⟩ := by
    simpa using slots (.fixed 0) (fixed 0)
  have root : readWord (batchExecutionState evm batch) evm.executionEnv.codeOwner ⟨1⟩ = ⟨batch.newRoot⟩ := by
    simpa using slots (.fixed 1) (fixed 1)
  have number : readWord (batchExecutionState evm batch) evm.executionEnv.codeOwner ⟨2⟩ =
      UInt256.ofNat batch.number := by
    simpa using slots (.fixed 2) (fixed 2)
  have backing : readWord (batchExecutionState evm batch) evm.executionEnv.codeOwner ⟨3⟩ =
      UInt256.ofNat (batchAvailable evm batch - batch.withdrawalAmount) := by
    simpa using slots (.fixed 3) (fixed 3)
  have balance := storeKeys_balance evm evm.executionEnv.codeOwner (batchWrites evm batch)
  rw [← batch_execution_writes] at balance
  have ethRead (state : Ethereum.State) :
      (project state evm.executionEnv.codeOwner keys).eth =
        (((state.lookupAccount evm.executionEnv.codeOwner).map (fun account : Account => account.balance)).getD (⟨0⟩ : UInt256)).toNat := by
    dsimp only [project]
    cases state.lookupAccount evm.executionEnv.codeOwner <;> rfl
  have eth : (project (batchExecutionState evm batch) evm.executionEnv.codeOwner keys).eth =
      (project evm evm.executionEnv.codeOwner keys).eth := by
    rw [ethRead, ethRead, balance]
  have numberNat := congrArg UInt256.toNat number
  rw [ulit_toNat' _ numberBound] at numberNat
  have backingNat := congrArg UInt256.toNat backing
  rw [ulit_toNat' _ backingBound, reads.2.1] at backingNat
  simpa only [project, executeBatch, seq, root, numberNat, backingNat, pending, claims,
    Rollup.State.mk.injEq, true_and, and_true] using eth

end Rollup.EVM
