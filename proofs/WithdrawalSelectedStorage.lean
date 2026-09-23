import proofs.WithdrawalSelectedPrefix
import proofs.ActiveCallbackStorage

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- The receiver tree cannot change the locked rollup's code or storage. -/
theorem withdrawal_selected_active_storage (before current : Ethereum.State)
    (owner : Address) (value : UInt256) (keys : AccessScope) (call : MessageCall) (selectedCode : ByteArray)
    (code : OwnCode before) (world : WorldBounded before)
    (ready : StorageReady before before.executionEnv.codeOwner keys)
    (safe : Safe (project before before.executionEnv.codeOwner keys))
    (enabled : WithdrawalEnabled (project before before.executionEnv.codeOwner keys) owner value.toNat)
    (accounts : call.accounts = (withdrawalLockedState before).accountMap)
    (sender : call.sender = before.executionEnv.codeOwner) (receiver : call.receiver = owner)
    (amount : call.value = value) (selected : toExecute call.accounts call.receiver = .Code selectedCode)
    (trace : ActivePrefix (call.codeEntry selectedCode) current) :
    CodeStorageFrame before.executionEnv.codeOwner (withdrawalLockedState before).accountMap current.accountMap := by
  have entered : (call.codeEntry selectedCode).accountMap =
      sendEth owner before.executionEnv.codeOwner value true (withdrawalLockedState before).accountMap := by
    change sendEth call.receiver call.sender call.value true call.accounts = _
    rw [accounts, sender, receiver, amount]
  obtain ⟨locked, entrySafe⟩ := withdrawal_transfer_safe before owner value keys code world ready safe enabled
  have entryLocked : LockedWorld before.executionEnv.codeOwner (call.codeEntry selectedCode).accountMap := by
    rwa [entered]
  have transfer : CodeStorageFrame before.executionEnv.codeOwner (withdrawalLockedState before).accountMap
      (call.codeEntry selectedCode).accountMap := by
    rw [entered]
    exact sendEth_accountStaticStateEq _ _ _ _ _ _
  by_cases foreign : before.executionEnv.codeOwner ≠ (call.codeEntry selectedCode).executionEnv.codeOwner
  · apply transfer.trans
    apply callback_active_storage keys ⟨owner, value.toNat, (project before before.executionEnv.codeOwner keys).eth⟩
      foreign entryLocked _ trace
    simpa only [inFlightProjection, project_boundary, entered, accountView] using entrySafe
  · have same : call.receiver = before.executionEnv.codeOwner := (not_ne_iff.mp foreign).symm
    have pinned : (call.accounts.findD before.executionEnv.codeOwner default).code = runtimeBytecode := by
      rw [accounts]
      exact LockedWorld.pinned (withdrawal_locked_world code world)
    have chosen := selected_pinned_code pinned (same ▸ selected)
    have unchanged := locked_active_accounts (start := call.codeEntry selectedCode) (current := current)
      chosen rfl rfl (by
        change readWord _ call.receiver ⟨6⟩ ≠ ⟨0⟩
        rw [same, readWord_default]
        exact LockedWorld.locked entryLocked) trace
    rwa [unchanged]

end Rollup.EVM
