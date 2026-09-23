import proofs.MessageTree
import semantics.recording.ExecutionTreeComplete
import proofs.WorldPrecompiles
import proofs.RollupCallOpcode

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- The complete execution record connects a code result to its message boundary. -/
theorem message_execution_refines (call : MessageCall) (code : ByteArray) {self : Address} {keys : AccessScope}
    {created accounts gas substate accepted output}
    (executed : call.run code = (created, accounts, gas, substate, accepted, output))
    (ready : BoundaryReady self call.accounts keys) (safe : Safe (boundaryModel self call.accounts keys))
    (senderSafe : self ≠ call.sender ∨ call.value = ⟨0⟩)
    (funds : call.value.toNat ≤ ethLedger call.accounts call.sender)
    (frame : FrameResultRefines self keys call.initialAccounts
      (X ((call.codeEntry code).machineState.gasAvailable.toNat + 1) (D_J code 0) (call.codeEntry code))) :
    BoundaryRefines self keys call.accounts accounts := by
  obtain ⟨tree⟩ := frame_run_complete ((call.codeEntry code).machineState.gasAvailable.toNat + 1)
    (D_J code 0) (call.codeEntry code)
  exact message_tree_refines call code tree executed ready safe senderSafe funds frame

/-- A call helper commits its code result, a precompile transfer, or its original accounts. -/
theorem call_site_tree_refines (site : CallSite) (before after : Ethereum.State)
    {self : Address} {keys : AccessScope} {returned : UInt256}
    (ready : BoundaryReady self before.accountMap keys)
    (safe : Safe (boundaryModel self before.accountMap keys))
    (senderSafe : self ≠ (site.message before).sender ∨ site.value = ⟨0⟩)
    (source : AccountAddress.ofUInt256 site.source = before.executionEnv.codeOwner ∨ site.value = ⟨0⟩)
    (frames : ∀ code,
      site.enabled before →
      toExecute before.accountMap (AccountAddress.ofUInt256 site.target) = .Code code →
      FrameResultRefines self keys (site.message before).initialAccounts
        (X (((site.message before).codeEntry code).machineState.gasAvailable.toNat + 1)
          (D_J code 0) ((site.message before).codeEntry code)))
    (run : site.run before = .ok (returned, after)) :
    BoundaryRefines self keys before.accountMap after.accountMap := by
  by_cases enabled : site.enabled before
  · have funds := call_site_funded site before enabled source
    have accountsSame := call_site_outcome site before after returned enabled run
    rcases outcome : site.outcome before with ⟨created, accounts, gas, substate, accepted, output⟩
    rw [outcome] at accountsSame
    rw [accountsSame]
    cases selected : toExecute before.accountMap (AccountAddress.ofUInt256 site.target) with
    | Code code =>
      rw [call_site_code site before code selected] at outcome
      exact message_execution_refines (site.message before) code outcome ready safe senderSafe funds
        (frames code enabled selected)
    | Precompiled pc =>
      unfold CallSite.outcome at outcome
      rw [selected] at outcome
      rcases precompiled_call_accounts outcome with restored | transferred
      · rw [restored]
        exact ⟨ready, safe, .initial⟩
      · rw [transferred]
        exact boundary_transfer_refines self (site.message before).sender (site.message before).receiver
          before.accountMap site.value keys ready safe senderSafe funds
  · rw [call_site_disabled_accounts site before after returned enabled run]
    exact ⟨ready, safe, .initial⟩

end Rollup.EVM
