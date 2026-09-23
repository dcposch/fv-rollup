import proofs.CallbackPayment
import proofs.StorageWrites

open Solm Ethereum Reasoning.Theory

namespace Rollup.EVM

def withdrawalFinalWrites (before : Ethereum.State) (owner : Address) (amount : Nat) :
    List (StorageKey × UInt256) :=
  [(.claims owner, UInt256.ofNat (withdrawalCredit before owner - amount)), (.fixed 6, ⟨0⟩)]

theorem withdrawal_final_writes (before after : Ethereum.State) (owner : Address) (amount : Nat)
    (environment : after.executionEnv = before.executionEnv) :
    withdrawalFinalState before after owner amount =
      storeKeys after before.executionEnv.codeOwner (withdrawalFinalWrites before owner amount) := by
  simp only [withdrawalFinalState, withdrawalDebitedState, withdrawalFinalWrites,
    storeKeys, keySlot, environment]
  rfl

/-- The callback and final writes keep the storage scope and pinned code. -/
theorem withdrawal_final_storage_ready {before after : Ethereum.State} {owner : Address}
    {amount : Nat} {output : ByteArray} (keys : AccessScope)
    (code : OwnCode before) (ready : StorageReady before before.executionEnv.codeOwner keys)
    (claimsKey : StorageKey.claims owner ∈ keys)
    (call : callViaEVM (withdrawalLockedState before) owner amount ByteArray.empty (true, after, output)) :
    StorageReady (withdrawalFinalState before after owner amount) before.executionEnv.codeOwner keys ∧
    OwnCode (withdrawalFinalState before after owner amount) := by
  have lockKey : StorageKey.fixed 6 ∈ keys := ready.1 (by simp [fixedKeys])
  have lockedReady : StorageReady (withdrawalLockedState before) before.executionEnv.codeOwner keys :=
    ⟨ready.1, ready.2.1, sparse_store ready.2.2 lockKey ⟨1⟩⟩
  have frame := withdrawal_callback_storage code call
  have afterReady := frame.storageReady lockedReady
  have lockedCode : OwnCode (withdrawalLockedState before) := ownCode_store _ _ _ _ code
  have frame' : CodeStorageFrame (withdrawalLockedState before).executionEnv.codeOwner
      (withdrawalLockedState before).accountMap after.accountMap := by
    simpa only [withdrawalLockedState, storageStore_executionEnv] using frame
  have afterCode := frame'.ownCode (source_callback_environment call) lockedCode
  have environment : after.executionEnv = before.executionEnv := by
    simpa only [withdrawalLockedState, storageStore_executionEnv] using source_callback_environment call
  rw [withdrawal_final_writes before after owner amount environment]
  refine ⟨storeKeys_ready after _ _ keys afterReady ?_, storeKeys_ownCode _ _ _ afterCode⟩
  intro write member
  simp only [withdrawalFinalWrites, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact claimsKey
  · exact lockKey

/-- A completed payment debits only the owner's credit and clears the lock. -/
theorem withdrawal_final_storage_values {before after : Ethereum.State} {owner : Address}
    {amount : Nat} {output : ByteArray} (keys : AccessScope)
    (code : OwnCode before) (ready : StorageReady before before.executionEnv.codeOwner keys)
    (claimsKey : StorageKey.claims owner ∈ keys)
    (unlocked : readWord before before.executionEnv.codeOwner ⟨6⟩ = ⟨0⟩)
    (call : callViaEVM (withdrawalLockedState before) owner amount ByteArray.empty (true, after, output))
    (key : StorageKey) (tracked : key ∈ keys) :
    readWord (withdrawalFinalState before after owner amount) before.executionEnv.codeOwner (keySlot key) =
      if key = .claims owner then UInt256.ofNat (withdrawalCredit before owner - amount)
      else readWord before before.executionEnv.codeOwner (keySlot key) := by
  have lockKey : StorageKey.fixed 6 ∈ keys := ready.1 (by simp [fixedKeys])
  have frame := withdrawal_callback_storage code call
  have pinned := ownCode_default code
  obtain ⟨account, found, _⟩ := pinned_account_present pinned
  have lockedCode : OwnCode (withdrawalLockedState before) := ownCode_store _ _ _ _ code
  have lockedPinned : ((withdrawalLockedState before).accountMap.findD before.executionEnv.codeOwner
      default).code = runtimeBytecode := by
    simpa only [withdrawalLockedState, storageStore_executionEnv] using ownCode_default lockedCode
  have afterPinned := frame.2.2.symm.trans lockedPinned
  obtain ⟨afterAccount, afterFound, _⟩ := pinned_account_present afterPinned
  have environment : after.executionEnv = before.executionEnv := by
    simpa only [withdrawalLockedState, storageStore_executionEnv] using source_callback_environment call
  rw [withdrawal_final_writes before after owner amount environment]
  have slots := read_storeKeys after before.executionEnv.codeOwner
    (withdrawalFinalWrites before owner amount) keys key ⟨afterAccount, afterFound⟩ ready.2.1 tracked
    (by
      intro write member
      simp only [withdrawalFinalWrites, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact claimsKey
      · exact lockKey)
  rw [slots, ← frame.readWord (keySlot key)]
  have initial := read_store_key found ready.2.1 tracked lockKey ⟨1⟩
  change readWord (withdrawalLockedState before) before.executionEnv.codeOwner (keySlot key) = _ at initial
  rw [initial]
  by_cases lock : key = .fixed 6
  · subst key
    simpa only [withdrawalFinalWrites, writtenWord, reduceCtorEq, if_true, if_false] using unlocked.symm
  · simp [withdrawalFinalWrites, writtenWord, lock]

end Rollup.EVM
