import proofs.ChildCall
import proofs.LockedFrame

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- Every funded child entry preserves the lock and the payment reservation. -/
theorem call_site_entry_safe (site : CallSite) (before : Ethereum.State)
    (self : Address) (keys : AccessScope) (payment : Payment) (code : ByteArray)
    (enabled : site.enabled before)
    (source : AccountAddress.ofUInt256 site.source = before.executionEnv.codeOwner ∨ site.value = ⟨0⟩)
    (foreign : self ≠ before.executionEnv.codeOwner)
    (initial : LockedWorld self before.accountMap)
    (safe : Safe (inFlightProjection before self keys payment)) :
    LockedWorld self ((site.message before).codeEntry code).accountMap ∧
      Safe (inFlightProjection ((site.message before).codeEntry code) self keys payment) := by
  have safeSender : self ≠ (site.message before).sender ∨ site.value = ⟨0⟩ := by
    rcases source with source | zero
    · exact .inl (by simpa only [CallSite.message, source] using foreign)
    · exact .inr zero
  exact callback_transfer_safe before ((site.message before).codeEntry code)
    self (site.message before).sender (site.message before).receiver site.value keys payment
    safeSender initial safe (call_site_funded site before enabled source) rfl

/-- Actual call prechecks and arguments establish safety at the child entry. -/
theorem child_call_entry_safe {before child : Ethereum.State} {jumps : Array UInt256}
    {self : Address} (keys : AccessScope) (payment : Payment)
    (entered : ChildCallEntry jumps before child) (foreign : self ≠ before.executionEnv.codeOwner)
    (initial : LockedWorld self before.accountMap) (safe : Safe (inFlightProjection before self keys payment)) :
    LockedWorld self child.accountMap ∧ Safe (inFlightProjection child self keys payment) := by
  cases entered with
  | @entered op arg checked cost site code instruction precheck arguments enabled selected =>
    have accounts := precheck_accounts precheck
    have environment := Z_executionEnv_eq precheck
    have checkedForeign : self ≠ checked.executionEnv.codeOwner := by simpa only [environment] using foreign
    have checkedInitial : LockedWorld self checked.accountMap := by rwa [accounts]
    have checkedSafe : Safe (inFlightProjection (callParent
        { checked with executionEnv.depth := before.executionEnv.depth }) self keys payment) := by
      simpa only [inFlightProjection, project_boundary, callParent, accounts] using safe
    exact call_site_entry_safe site _ self keys payment code enabled
      (call_opcode_source arguments) checkedForeign checkedInitial checkedSafe

/-- A selected code branch at a pinned account uses that account's runtime. -/
theorem selected_pinned_code {accounts : AccountMap} {self : Address} {code : ByteArray}
    (pinned : (accounts.findD self default).code = runtimeBytecode)
    (selected : toExecute accounts self = .Code code) : code = runtimeBytecode := by
  obtain ⟨account, found, codeEq⟩ := pinned_account_present pinned
  unfold toExecute at selected
  split at selected
  · cases selected
  · simp only [found, Id.run] at selected
    exact (ToExecute.Code.inj selected).symm.trans codeEq

/-- A nested call into the locked rollup preserves all accounts at each active prefix. -/
theorem child_call_locked_active_accounts {before child current : Ethereum.State}
    {jumps : Array UInt256} {self : Address}
    (entered : ChildCallEntry jumps before child) (foreign : self ≠ before.executionEnv.codeOwner)
    (pinned : (before.accountMap.findD self default).code = runtimeBytecode)
    (initial : LockedWorld self child.accountMap) (owner : child.executionEnv.codeOwner = self)
    (trace : ActivePrefix child current) : current.accountMap = child.accountMap := by
  cases entered with
  | @entered op arg checked cost site code instruction precheck arguments enabled selected =>
    have accounts := precheck_accounts precheck
    have environment := Z_executionEnv_eq precheck
    have checkedForeign : self ≠ checked.executionEnv.codeOwner := by simpa only [environment] using foreign
    have receiver : AccountAddress.ofUInt256 site.recipient = self := owner
    have target := call_opcode_target checkedForeign arguments receiver
    rw [target] at selected
    have chosen := selected_pinned_code (by simpa only [accounts] using pinned) selected
    apply locked_active_accounts chosen rfl rfl _ trace
    change readWord _ (AccountAddress.ofUInt256 site.recipient) ⟨6⟩ ≠ ⟨0⟩
    rw [receiver, readWord_default]
    exact LockedWorld.locked initial

end Rollup.EVM
