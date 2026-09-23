import semantics.ExecutionScope
import proofs.RecordedExecution
import proofs.CallTree

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- A complete foreign message preserves the rollup, with no child-correctness premise. -/
theorem foreign_message_refines (call : MessageCall) (code : ByteArray) {self : Address} {keys : AccessScope}
    {created accounts gas substate accepted output}
    (executed : call.run code = (created, accounts, gas, substate, accepted, output))
    (ordinary : self ∉ π) (foreign : self ≠ call.receiver)
    (ready : BoundaryReady self call.accounts keys) (safe : Safe (boundaryModel self call.accounts keys))
    (senderSafe : self ≠ call.sender ∨ call.value = ⟨0⟩)
    (funds : call.value.toNat ≤ ethLedger call.accounts call.sender)
    (scope : messageCodeScope call code self ⊆ keys) :
    BoundaryRefines self keys call.accounts accounts := by
  have transfer := boundary_transfer_refines self call.sender call.receiver call.accounts call.value keys
    ready safe senderSafe funds
  apply message_execution_refines call code executed ready safe senderSafe funds
  exact foreign_execution_refines _ _ (call.codeEntry code) self keys ordinary foreign
    transfer.1 transfer.2.1 scope

/-- Actual code selection also covers foreign precompile messages. -/
theorem foreign_selected_message_refines (call : MessageCall) {self : Address} {keys : AccessScope}
    {created accounts gas substate accepted output}
    (executed : call.selectedRun = (created, accounts, gas, substate, accepted, output))
    (ordinary : self ∉ π) (foreign : self ≠ call.receiver)
    (ready : BoundaryReady self call.accounts keys) (safe : Safe (boundaryModel self call.accounts keys))
    (senderSafe : self ≠ call.sender ∨ call.value = ⟨0⟩)
    (funds : call.value.toNat ≤ ethLedger call.accounts call.sender)
    (scope : selectedMessageScope call self ⊆ keys) :
    BoundaryRefines self keys call.accounts accounts := by
  unfold MessageCall.selectedRun at executed
  unfold selectedMessageScope at scope
  cases selected : toExecute call.accounts call.receiver with
  | Code code =>
    rw [selected] at executed scope
    exact foreign_message_refines call code executed ordinary foreign ready safe senderSafe funds scope
  | Precompiled pc =>
    rw [selected] at executed
    rcases precompiled_call_accounts executed with restored | transferred
    · rw [restored]
      exact ⟨ready, safe, .initial⟩
    · rw [transferred]
      exact boundary_transfer_refines self call.sender call.receiver call.accounts call.value keys
        ready safe senderSafe funds

/-- A funded external message can target the rollup, another contract, or a precompile. -/
theorem selected_message_refines (call : MessageCall) (result : MessageResult)
    {self : Address} {keys : AccessScope}
    (executed : call.selectedRun = result.tuple)
    (ordinary : self ∉ π) (sender : self ≠ call.sender)
    (context : call.contextValue = call.value) (bounded : call.calldata.size < UInt256.size)
    (ready : BoundaryReady self call.accounts keys) (safe : Safe (boundaryModel self call.accounts keys))
    (funds : call.value.toNat ≤ ethLedger call.accounts call.sender)
    (scope : selectedMessageScope call self ⊆ keys) :
    BoundaryRefines self keys call.accounts result.accounts := by
  by_cases receiver : call.receiver = self
  · subst self
    have selected := pinned_toExecute ordinary (BoundaryReady.pinned ready)
    unfold selectedMessageScope at scope
    rw [selected] at scope
    have entry := frame_run_entry_covered
      (executionRecord ((call.codeEntry runtimeBytecode).machineState.gasAvailable.toNat + 1)
        (D_J runtimeBytecode 0) (call.codeEntry runtimeBytecode)) rfl
    have access : CalldataCovered call.entryState keys := Finset.Subset.trans entry scope
    have event := ExecutionStep.message call result ⟨rfl, sender, context, funds, bounded⟩ executed
    have effect := execution_step_refines ordinary ready safe event access
    exact ⟨effect.1, effect.2.1, effect.2.2.1⟩
  · exact foreign_selected_message_refines call executed ordinary (Ne.symm receiver) ready safe
      (.inl sender) funds scope

end Rollup.EVM
