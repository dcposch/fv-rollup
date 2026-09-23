import proofs.CallbackStorage
import proofs.CallbackProjection
import proofs.WithdrawalExecution
import proofs.World

open Solm Ethereum Ethereum.EVM Reasoning.Theory

namespace Rollup.EVM

/-- The caller resumes in its original execution environment. -/
theorem source_callback_environment {before after : Ethereum.State} {owner : Address}
    {value : Int} {input output : ByteArray} {accepted writable : Bool}
    (call : callViaEVM before owner value input (accepted, after, output) writable) :
    after.executionEnv = before.executionEnv := by
  cases call <;> subst_vars <;> rfl

/-- An external source call preserves the locked rollup's code and storage. -/
theorem source_callback_storage {before after : Ethereum.State} {owner : Address}
    {value : Int} {input output : ByteArray} {accepted writable : Bool}
    (pinned : (before.accountMap.findD before.executionEnv.codeOwner default).code = runtimeBytecode)
    (locked : (before.accountMap.findD before.executionEnv.codeOwner default).storage.findD ⟨6⟩ ⟨0⟩ ≠ ⟨0⟩)
    (call : callViaEVM before owner value input (accepted, after, output) writable) :
    CodeStorageFrame before.executionEnv.codeOwner before.accountMap after.accountMap := by
  cases call with
  | callMade word payment state balance depth =>
    obtain ⟨gas, substate, run⟩ := payment
    subst after
    exact callback_preserves_rollup_storage _ pinned locked run.symm
  | callNotMade substate state rejected =>
    subst after
    exact CodeStorageFrame.refl _ _

/-- A withdrawal callback preserves every slot after lock acquisition. -/
theorem withdrawal_callback_storage {before after : Ethereum.State} {owner : Address}
    {amount : Nat} {output : ByteArray}
    (code : OwnCode before)
    (call : callViaEVM (withdrawalLockedState before) owner amount ByteArray.empty
      (true, after, output)) :
    CodeStorageFrame before.executionEnv.codeOwner
      (withdrawalLockedState before).accountMap after.accountMap := by
  have lockedCode : OwnCode (withdrawalLockedState before) := ownCode_store _ _ _ _ code
  have pinned := ownCode_default code
  obtain ⟨account, found, _⟩ := pinned_account_present pinned
  have lockValue : readWord (withdrawalLockedState before) before.executionEnv.codeOwner ⟨6⟩ = ⟨1⟩ :=
    storageLoad_storageStore_same_present before before.executionEnv.codeOwner found ⟨6⟩ ⟨1⟩
  have locked : ((withdrawalLockedState before).accountMap.findD before.executionEnv.codeOwner
      default).storage.findD ⟨6⟩ ⟨0⟩ ≠ ⟨0⟩ := by
    rw [← readWord_default, lockValue]
    decide
  have frame := source_callback_storage (before := withdrawalLockedState before)
    (ownCode_default lockedCode)
    (by simpa only [withdrawalLockedState, storageStore_executionEnv] using locked) call
  simpa only [withdrawalLockedState, storageStore_executionEnv] using frame

end Rollup.EVM
