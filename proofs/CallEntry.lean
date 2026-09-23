import semantics.CallEntry
import proofs.CallbackEntry
import proofs.MessageValue

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- The code execution function starts at the message's fresh execution state. -/
theorem message_execute_entry (message : MessageCall) (code : ByteArray) :
    message.execute code = (do
      let result ← X (message.gas.toNat + 1) (D_J code 0) (message.codeEntry code)
      match result with
      | .success state output =>
        pure (.success (state.createdAccounts, state.accountMap,
          state.machineState.gasAvailable.toUInt256, state.substate) output)
      | .revert gas output => pure (.revert gas output)) := by
  unfold MessageCall.execute Ξ
  rfl

/-- The call guard supplies the actual transfer source with enough ETH. -/
theorem call_site_funded (site : CallSite) (before : Ethereum.State)
    (enabled : site.enabled before)
    (source : AccountAddress.ofUInt256 site.source = before.executionEnv.codeOwner ∨ site.value = ⟨0⟩) :
    site.value.toNat ≤ ethLedger before.accountMap (site.message before).sender := by
  rcases source with source | zero
  · change site.value.toNat ≤ ethLedger before.accountMap (AccountAddress.ofUInt256 site.source)
    rw [source, ethLedger_lookup]
    have enough := enabled.1
    change site.value.toNat ≤ (Option.option (⟨0⟩ : UInt256) (fun (x : Account) => x.balance)
      (before.accountMap.find? before.executionEnv.codeOwner)).toNat at enough
    cases found : before.accountMap.find? before.executionEnv.codeOwner <;>
      simpa [found, Option.option, UInt256.toNat] using enough
  · simp [zero, UInt256.toNat]

/-- A started helper returns the account map produced by the selected child message. -/
theorem call_site_outcome (site : CallSite) (before after : Ethereum.State) (result : UInt256)
    (enabled : site.enabled before) (run : site.run before = .ok (result, after)) :
    after.accountMap = (site.outcome before).2.1 := by
  unfold CallSite.run call at run
  simp only [enabled.1, enabled.2, and_self, if_true] at run
  have same := congrArg Prod.snd (Except.ok.inj run)
  exact (congrArg Ethereum.State.accountMap same).symm

/-- The selected code branch uses the same message and fresh execution state. -/
theorem call_site_code (site : CallSite) (before : Ethereum.State) (code : ByteArray)
    (selected : toExecute before.accountMap (AccountAddress.ofUInt256 site.target) = .Code code) :
    site.outcome before = (site.message before).run code := by
  unfold CallSite.outcome
  rw [selected]
  rfl

/-- A foreign child frame keeps the payment reservation at each instruction boundary. -/
theorem call_site_prefix_safe (site : CallSite) (before current : Ethereum.State)
    (self : Address) (keys : AccessScope) (payment : Payment) (code : ByteArray)
    (enabled : site.enabled before)
    (source : AccountAddress.ofUInt256 site.source = before.executionEnv.codeOwner ∨ site.value = ⟨0⟩)
    (foreign : self ≠ before.executionEnv.codeOwner)
    (receiver : self ≠ AccountAddress.ofUInt256 site.recipient)
    (initial : LockedWorld self before.accountMap)
    (safe : Safe (inFlightProjection before self keys payment))
    (trace : InstructionPrefix (D_J code 0) ((site.message before).codeEntry code) current) :
    LockedWorld self current.accountMap ∧ Safe (inFlightProjection current self keys payment) := by
  have safeSender : self ≠ (site.message before).sender ∨ site.value = ⟨0⟩ := by
    rcases source with source | zero
    · exact .inl (by simpa only [CallSite.message, source] using foreign)
    · exact .inr zero
  have transferred := callback_transfer_safe before ((site.message before).codeEntry code)
    self (site.message before).sender (site.message before).receiver site.value keys payment
    safeSender initial safe (call_site_funded site before enabled source) rfl
  have childForeign : self ≠ ((site.message before).codeEntry code).executionEnv.codeOwner := receiver
  exact ⟨(callback_instruction_prefix childForeign transferred.1 trace).2.2,
    callback_prefix_safe keys payment childForeign transferred.1 transferred.2 trace⟩

end Rollup.EVM
