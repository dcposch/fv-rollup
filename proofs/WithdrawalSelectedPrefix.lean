import proofs.WithdrawalActive

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- A selected withdrawal receiver preserves in-flight safety, including a payment to the rollup itself. -/
theorem withdrawal_selected_active_safe (before current : Ethereum.State)
    (owner : Address) (value : UInt256) (keys : AccessScope) (call : MessageCall) (selectedCode : ByteArray)
    (code : OwnCode before) (world : WorldBounded before)
    (ready : StorageReady before before.executionEnv.codeOwner keys)
    (safe : Safe (project before before.executionEnv.codeOwner keys))
    (enabled : WithdrawalEnabled (project before before.executionEnv.codeOwner keys) owner value.toNat)
    (accounts : call.accounts = (withdrawalLockedState before).accountMap)
    (sender : call.sender = before.executionEnv.codeOwner) (receiver : call.receiver = owner)
    (amount : call.value = value) (selected : toExecute call.accounts call.receiver = .Code selectedCode)
    (trace : ActivePrefix (call.codeEntry selectedCode) current) :
    Safe (inFlightProjection current before.executionEnv.codeOwner keys
      ⟨owner, value.toNat, (project before before.executionEnv.codeOwner keys).eth⟩) := by
  have entered : (call.codeEntry selectedCode).accountMap =
      sendEth owner before.executionEnv.codeOwner value true (withdrawalLockedState before).accountMap := by
    change sendEth call.receiver call.sender call.value true call.accounts = _
    rw [accounts, sender, receiver, amount]
  by_cases foreign : before.executionEnv.codeOwner ≠ (call.codeEntry selectedCode).executionEnv.codeOwner
  · exact withdrawal_callback_active_safe before _ current owner value keys code world ready safe enabled
      entered foreign trace
  · have same : call.receiver = before.executionEnv.codeOwner := (not_ne_iff.mp foreign).symm
    have lockedBefore := withdrawal_locked_world code world
    have pinned : (call.accounts.findD before.executionEnv.codeOwner default).code = runtimeBytecode := by
      rw [accounts]
      exact LockedWorld.pinned lockedBefore
    have chosen := selected_pinned_code pinned (same ▸ selected)
    obtain ⟨locked, entrySafe⟩ := withdrawal_transfer_safe before owner value keys code world ready safe enabled
    have entryLocked : LockedWorld before.executionEnv.codeOwner (call.codeEntry selectedCode).accountMap := by
      rwa [entered]
    have unchanged := locked_active_accounts (start := call.codeEntry selectedCode) (current := current)
      chosen rfl rfl (by
        change readWord _ call.receiver ⟨6⟩ ≠ ⟨0⟩
        rw [same, readWord_default]
        exact LockedWorld.locked entryLocked) trace
    simpa only [inFlightProjection, project_boundary, unchanged, entered, accountView] using entrySafe

end Rollup.EVM
