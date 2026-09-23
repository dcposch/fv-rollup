import proofs.MessageValue
import proofs.RuntimeRefinement

open Ethereum Ethereum.EVM Solm Reasoning.Theory Reasoning.Reach

namespace Rollup.EVM

/-- The EVM selects the stored runtime outside the precompile address set. -/
theorem message_selected_runtime (call : MessageCall) (keys : AccessScope)
    (ready : BoundaryReady call.receiver call.accounts keys) (ordinary : call.receiver ∉ π) :
    call.selectedRun = call.run runtimeBytecode := by
  unfold MessageCall.selectedRun MessageCall.run
  rw [pinned_toExecute ordinary (BoundaryReady.pinned ready)]

/-- A successful message call preserves boundary conditions and has the exact model effect. -/
theorem message_refines_model (call : MessageCall) (locals : Store) (label : Call) (keys : AccessScope)
    (ready : BoundaryReady call.receiver call.accounts keys)
    (safe : Safe (boundaryModel call.receiver call.accounts keys))
    (ordinary : call.receiver ∉ π) (different : call.receiver ≠ call.sender)
    (value : call.contextValue = call.value)
    (funds : call.value.toNat ≤ ethLedger call.accounts call.sender)
    (bounded : call.calldata.size < UInt256.size)
    (bound : CallBound call.entryState locals label)
    (accesses : entryKeys label.entry ⊆ keys)
    {created accounts gas substate output}
    (run : call.selectedRun = (created, accounts, gas, substate, true, output)) :
    BoundaryReady call.receiver accounts keys ∧
      ∃ result payments,
        CallStep (boundaryModel call.receiver call.accounts keys) label (.success result) payments
          (boundaryModel call.receiver accounts keys) ∧
        returnDataEquiv output (returnValues result) (.abi (entryTransition label.entry).returnType) := by
  rw [message_selected_runtime call keys ready ordinary] at run
  have execution := (message_call_accepted call runtimeBytecode created accounts gas substate output run).1
  have initial := message_entry_ready call keys ready different value funds
  have before := message_before_model call keys different value funds (BoundaryReady.world ready)
  have initialSafe : Safe (beforeCall call.entryState keys) := by rwa [before]
  obtain ⟨storage, unlocked, code, world, result, payments, step, returned⟩ :=
    runtime_refines_model (cA := call.created) (gh := call.genesis) (bl := call.blocks)
      (σ := call.initialAccounts) (σ₀ := call.original) (g := call.gas) (A := call.substate)
      (I := call.environment runtimeBytecode) locals label keys rfl bounded bound accesses
      initial.1 initial.2.1 initial.2.2.1 initial.2.2.2.1 initial.2.2.2.2 initialSafe execution
  refine ⟨boundary_ready_of_state code world storage unlocked, result, payments, ?_, returned⟩
  change CallStep (beforeCall call.entryState keys) label (.success result) payments
    (project (initState created call.genesis call.blocks accounts call.original (.ofUInt256 gas)
      substate (call.environment runtimeBytecode)) call.receiver keys) at step
  rw [before, project_boundary] at step
  exact step

/-- Successful message calls preserve custody, reservations, and word bounds. -/
theorem message_preserves_safe (call : MessageCall) (locals : Store) (label : Call) (keys : AccessScope)
    (ready : BoundaryReady call.receiver call.accounts keys)
    (safe : Safe (boundaryModel call.receiver call.accounts keys))
    (ordinary : call.receiver ∉ π) (different : call.receiver ≠ call.sender)
    (value : call.contextValue = call.value)
    (funds : call.value.toNat ≤ ethLedger call.accounts call.sender)
    (bounded : call.calldata.size < UInt256.size)
    (bound : CallBound call.entryState locals label)
    (accesses : entryKeys label.entry ⊆ keys)
    {created accounts gas substate output}
    (run : call.selectedRun = (created, accounts, gas, substate, true, output)) :
    Safe (boundaryModel call.receiver accounts keys) := by
  obtain ⟨_, _, _, step, _⟩ := message_refines_model call locals label keys ready safe ordinary different
    value funds bounded bound accesses run
  exact callStep_safe safe step

/-- A rejected message restores accounts and substate, including incoming ETH. -/
theorem message_rejected_boundary (call : MessageCall) (keys : AccessScope)
    (ready : BoundaryReady call.receiver call.accounts keys) (ordinary : call.receiver ∉ π)
    {created accounts gas substate output}
    (run : call.selectedRun = (created, accounts, gas, substate, false, output)) :
    accounts = call.accounts ∧ substate = call.substate := by
  rw [message_selected_runtime call keys ready ordinary] at run
  exact message_call_rejected call runtimeBytecode created accounts gas substate output run

end Rollup.EVM
