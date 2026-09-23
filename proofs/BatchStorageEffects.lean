import proofs.BatchExecution
import proofs.StorageWrites

open Solm Ethereum Reasoning.Theory

namespace Rollup.EVM

def batchWrites (evm : Ethereum.State) (batch : Batch) : List (StorageKey × UInt256) :=
  [(.fixed 6, ⟨1⟩),
   (.pending batch.depositOwner, UInt256.ofNat (batchDepositCredit evm batch - batch.depositAmount)),
   (.fixed 3, UInt256.ofNat (batchAvailable evm batch - batch.withdrawalAmount)),
   (.claims batch.withdrawalOwner, UInt256.ofNat (batchNextCredit evm batch)),
   (.fixed 1, ⟨batch.newRoot⟩), (.fixed 2, UInt256.ofNat batch.number), (.fixed 6, ⟨0⟩)]

theorem batch_execution_writes (evm : Ethereum.State) (batch : Batch) :
    batchExecutionState evm batch = storeKeys evm evm.executionEnv.codeOwner (batchWrites evm batch) := rfl

theorem batch_writes_tracked (evm : Ethereum.State) (batch : Batch) (keys : AccessScope)
    (fixed : fixedKeys ⊆ keys) (pending : StorageKey.pending batch.depositOwner ∈ keys)
    (claims : StorageKey.claims batch.withdrawalOwner ∈ keys) :
    ∀ write ∈ batchWrites evm batch, write.1 ∈ keys := by
  intro write member
  simp only [batchWrites, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact pending | exact claims | exact fixed (by simp [fixedKeys])

/-- The two mappings and fixed slots remain separate even when the owners coincide. -/
theorem batch_read_values (evm : Ethereum.State) (batch : Batch) (keys : AccessScope)
    (ready : StorageReady evm evm.executionEnv.codeOwner keys)
    (pending : StorageKey.pending batch.depositOwner ∈ keys)
    (claims : StorageKey.claims batch.withdrawalOwner ∈ keys) :
    batchDepositCredit evm batch = (project evm evm.executionEnv.codeOwner keys).pending batch.depositOwner ∧
    batchAvailable evm batch = (project evm evm.executionEnv.codeOwner keys).backing + batch.depositAmount ∧
    batchNextCredit evm batch = (project evm evm.executionEnv.codeOwner keys).claims batch.withdrawalOwner +
      batch.withdrawalAmount := by
  have fixed (i : Fin 7) : StorageKey.fixed i ∈ keys := ready.1 (by simp [fixedKeys])
  have separate {a b : StorageKey} (ha : a ∈ keys) (hb : b ∈ keys) (ne : a ≠ b) :
      keySlot a ≠ keySlot b := fun equal => ne (ready.2.1 a ha b hb equal)
  have pendingLock : keySlot (.pending batch.depositOwner) ≠ ⟨6⟩ :=
    separate pending (fixed 6) (by simp)
  have backingPending : (⟨3⟩ : UInt256) ≠ keySlot (.pending batch.depositOwner) :=
    separate (fixed 3) pending (by simp)
  have claimsBacking : keySlot (.claims batch.withdrawalOwner) ≠ ⟨3⟩ :=
    separate claims (fixed 3) (by simp)
  have claimsPending : keySlot (.claims batch.withdrawalOwner) ≠ keySlot (.pending batch.depositOwner) :=
    separate claims pending (by simp)
  have claimsLock : keySlot (.claims batch.withdrawalOwner) ≠ ⟨6⟩ :=
    separate claims (fixed 6) (by simp)
  have backingLock : (⟨3⟩ : UInt256) ≠ ⟨6⟩ := by decide
  refine ⟨?_, ?_, ?_⟩
  · simp only [batchDepositCredit, batchLockedState, readWord,
      storageLoad_storageStore_ne _ _ pendingLock,
      project, pendingLedger, pending, if_true]
  · simp only [batchAvailable, batchDebitedState, batchLockedState, readWord,
      storageLoad_storageStore_ne _ _ backingPending,
      storageLoad_storageStore_ne _ _ backingLock, project]
  · simp only [batchNextCredit, batchBackedState, batchDebitedState, batchLockedState, readWord,
      storageLoad_storageStore_ne _ _ claimsBacking,
      storageLoad_storageStore_ne _ _ claimsPending,
      storageLoad_storageStore_ne _ _ claimsLock, project, claimLedger, claims, if_true]

/-- Read any tracked key after the seven batch writes. -/
theorem batch_storage (evm : Ethereum.State) (batch : Batch) (keys : AccessScope)
    (present : ∃ account, evm.lookupAccount evm.executionEnv.codeOwner = some account)
    (ready : StorageReady evm evm.executionEnv.codeOwner keys)
    (pending : StorageKey.pending batch.depositOwner ∈ keys)
    (claims : StorageKey.claims batch.withdrawalOwner ∈ keys)
    (key : StorageKey) (tracked : key ∈ keys) :
    readWord (batchExecutionState evm batch) evm.executionEnv.codeOwner (keySlot key) =
      if key = .fixed 6 then ⟨0⟩
      else if key = .fixed 2 then UInt256.ofNat batch.number
      else if key = .fixed 1 then ⟨batch.newRoot⟩
      else if key = .claims batch.withdrawalOwner then UInt256.ofNat (batchNextCredit evm batch)
      else if key = .fixed 3 then UInt256.ofNat (batchAvailable evm batch - batch.withdrawalAmount)
      else if key = .pending batch.depositOwner then UInt256.ofNat (batchDepositCredit evm batch - batch.depositAmount)
      else readWord evm evm.executionEnv.codeOwner (keySlot key) := by
  rw [batch_execution_writes, read_storeKeys _ _ _ _ _ present ready.2.1 tracked
    (batch_writes_tracked evm batch keys ready.1 pending claims)]
  simp only [batchWrites, writtenWord]
  by_cases lock : key = .fixed 6
  · simp [lock]
  · simp only [lock, if_false]

end Rollup.EVM
