import semantics.Environment
import proofs.CallbackFrame
import proofs.World

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- Read a storage slot through the default account view. -/
theorem readWord_default (evm : Ethereum.State) (self : Address) (slot : UInt256) :
    readWord evm self slot = (evm.accountMap.findD self default).storage.findD slot ⟨0⟩ := by
  unfold readWord Solm.EVM.storageLoad Ethereum.State.lookupAccount Batteries.RBMap.findD
  cases evm.accountMap.find? self <;> rfl

/-- Code ownership supplies the pinned account view. -/
theorem ownCode_default {evm : Ethereum.State} (code : OwnCode evm) :
    (evm.accountMap.findD evm.executionEnv.codeOwner default).code = runtimeBytecode := by
  have present := code.2
  unfold Ethereum.State.lookupAccount at present
  cases found : evm.accountMap.find? evm.executionEnv.codeOwner with
  | none => simp [found] at present
  | some account =>
    simpa [Batteries.RBMap.findD, found] using Option.some.inj
      (by simpa only [found, Option.map_some] using present)

theorem CodeStorageFrame.readWord {before after : Ethereum.State} {self : Address}
    (frame : CodeStorageFrame self before.accountMap after.accountMap) (slot : UInt256) :
    readWord before self slot = readWord after self slot := by
  rw [readWord_default, readWord_default, frame.1]

theorem CodeStorageFrame.storageReady {before after : Ethereum.State} {self : Address}
    {keys : AccessScope} (frame : CodeStorageFrame self before.accountMap after.accountMap)
    (ready : StorageReady before self keys) : StorageReady after self keys := by
  refine ⟨ready.1, ready.2.1, ?_⟩
  intro slot outside
  rw [← frame.readWord slot]
  exact ready.2.2 slot outside

theorem CodeStorageFrame.ownCode {before after : Ethereum.State}
    (frame : CodeStorageFrame before.executionEnv.codeOwner before.accountMap after.accountMap)
    (environment : after.executionEnv = before.executionEnv)
    (code : OwnCode before) : OwnCode after := by
  have pinned := frame.2.2.symm.trans (ownCode_default code)
  obtain ⟨account, found, pinned⟩ := pinned_account_present pinned
  refine ⟨by rw [environment]; exact code.1, ?_⟩
  simp only [environment, Ethereum.State.lookupAccount, found, Option.map_some, pinned]

/-- The storage frame fixes all model fields except the ETH balance. -/
theorem CodeStorageFrame.project {before after : Ethereum.State} {self : Address}
    (frame : CodeStorageFrame self before.accountMap after.accountMap) (keys : AccessScope) :
    project after self keys =
      { project before self keys with eth := (project after self keys).eth } := by
  have reads (slot : UInt256) := frame.readWord slot
  have pending : pendingLedger after self keys = pendingLedger before self keys := by
    funext owner
    simp only [pendingLedger, ← reads]
  have claims : claimLedger after self keys = claimLedger before self keys := by
    funext owner
    simp only [claimLedger, ← reads]
  simp only [Rollup.EVM.project, pending, claims, ← reads]

end Rollup.EVM
