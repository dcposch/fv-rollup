import proofs.TreeBudget
import proofs.RecordedExecution
import proofs.SurroundingMessage
import proofs.SurroundingCreation

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- Actual foreign execution preserves the budget over its complete finite record. -/
theorem foreign_execution_budget (fuel : Nat) (jumps : Array UInt256) (start : Ethereum.State)
    (self : Address) (keys : AccessScope)
    (ordinary : self ∉ π) (foreign : self ≠ start.executionEnv.codeOwner)
    (ready : BoundaryReady self start.accountMap keys)
    (safe : Safe (boundaryModel self start.accountMap keys))
    (scope : (executionRecord fuel jumps start).scope self ⊆ keys) :
    FrameResultBudget start.accountMap (X fuel jumps start) :=
  frame_run_budget _ self keys ordinary foreign ready safe
    (execution_record_covered fuel jumps start self keys scope)

/-- A foreign code message preserves total ETH without a child-budget premise. -/
theorem foreign_message_budget (call : MessageCall) (code : ByteArray) {self : Address} {keys : AccessScope}
    {created accounts gas substate accepted output}
    (executed : call.run code = (created, accounts, gas, substate, accepted, output))
    (ordinary : self ∉ π) (foreign : self ≠ call.receiver)
    (ready : BoundaryReady self call.accounts keys) (safe : Safe (boundaryModel self call.accounts keys))
    (senderSafe : self ≠ call.sender ∨ call.value = ⟨0⟩)
    (funds : call.value.toNat ≤ ethLedger call.accounts call.sender)
    (scope : messageCodeScope call code self ⊆ keys) :
    worldEth accounts ≤ worldEth call.accounts := by
  have transfer := boundary_transfer_refines self call.sender call.receiver call.accounts call.value keys
    ready safe senderSafe funds
  apply message_execution_budget call code executed (BoundaryReady.world ready) funds
  exact foreign_execution_budget _ _ (call.codeEntry code) self keys ordinary foreign
    transfer.1 transfer.2.1 scope

/-- Foreign message budgets include the actual precompile or code selection. -/
theorem foreign_selected_message_budget (call : MessageCall) {self : Address} {keys : AccessScope}
    {created accounts gas substate accepted output}
    (executed : call.selectedRun = (created, accounts, gas, substate, accepted, output))
    (ordinary : self ∉ π) (foreign : self ≠ call.receiver)
    (ready : BoundaryReady self call.accounts keys) (safe : Safe (boundaryModel self call.accounts keys))
    (senderSafe : self ≠ call.sender ∨ call.value = ⟨0⟩)
    (funds : call.value.toNat ≤ ethLedger call.accounts call.sender)
    (scope : selectedMessageScope call self ⊆ keys) :
    worldEth accounts ≤ worldEth call.accounts := by
  unfold MessageCall.selectedRun at executed
  unfold selectedMessageScope at scope
  cases selected : toExecute call.accounts call.receiver with
  | Code code =>
    rw [selected] at executed scope
    exact foreign_message_budget call code executed ordinary foreign ready safe senderSafe funds scope
  | Precompiled pc =>
    rw [selected] at executed
    exact (precompiled_call_world funds (BoundaryReady.world ready) executed).le

/-- A complete external message to any receiver preserves total ETH. -/
theorem selected_message_budget (call : MessageCall) (result : MessageResult)
    {self : Address} {keys : AccessScope}
    (executed : call.selectedRun = result.tuple)
    (ordinary : self ∉ π) (sender : self ≠ call.sender)
    (context : call.contextValue = call.value) (bounded : call.calldata.size < UInt256.size)
    (ready : BoundaryReady self call.accounts keys) (safe : Safe (boundaryModel self call.accounts keys))
    (funds : call.value.toNat ≤ ethLedger call.accounts call.sender)
    (scope : selectedMessageScope call self ⊆ keys) :
    worldEth result.accounts ≤ worldEth call.accounts := by
  by_cases receiver : call.receiver = self
  · subst self
    have selected := pinned_toExecute ordinary (BoundaryReady.pinned ready)
    unfold selectedMessageScope at scope
    rw [selected] at scope
    have entry := frame_run_entry_covered
      (executionRecord ((call.codeEntry runtimeBytecode).machineState.gasAvailable.toNat + 1)
        (D_J runtimeBytecode 0) (call.codeEntry runtimeBytecode)) rfl
    have access : CalldataCovered call.entryState keys := Finset.Subset.trans entry scope
    exact rollup_message_world_nonincrease call keys ready ordinary sender context funds bounded access executed
  · exact foreign_selected_message_budget call executed ordinary (Ne.symm receiver) ready safe
      (.inl sender) funds scope

/-- Actual contract creation preserves total ETH across all nested calls. -/
theorem foreign_creation_budget (call : CreationCall) {self : Address} {keys : AccessScope}
    {address created accounts gas substate accepted output}
    (executed : call.run = (address, created, accounts, gas, substate, accepted, output))
    (ordinary : self ∉ π) (foreign : self ≠ call.sender)
    (ready : BoundaryReady self call.accounts keys) (safe : Safe (boundaryModel self call.accounts keys))
    (nonce : (call.accounts.findD call.sender default).nonce ≠ ⟨0⟩)
    (funds : call.value.toNat ≤ ethLedger call.accounts call.sender)
    (scope : creationExecutionScope call self ⊆ keys) :
    worldEth accounts ≤ worldEth call.accounts := by
  apply creation_execution_budget call executed (BoundaryReady.world ready) nonce funds
  intro fresh
  have receiver := creation_fresh_foreign call (BoundaryReady.pinned ready) fresh
  have different := creation_fresh_not_sender call nonce fresh
  have transfer := boundary_creation_transfer_refines self call.sender call.address call.accounts call.value keys
    ready safe foreign different funds
  exact foreign_execution_budget _ _ call.entryState self keys ordinary receiver
    transfer.1 transfer.2.1 scope

end Rollup.EVM
