import semantics.CallScope
import proofs.RuntimeSuccess
import proofs.CalldataScope
import proofs.MessageRefinement

open Ethereum Ethereum.EVM Solm Reasoning.Theory

namespace Rollup.EVM

/-- Actual successful bytecode supplies the message's decoded call label. -/
theorem message_accepted_call_bound (call : MessageCall) (keys : AccessScope)
    (ready : BoundaryReady call.receiver call.accounts keys)
    (ordinary : call.receiver ∉ π)
    (bounded : call.calldata.size < UInt256.size)
    {created accounts gas substate output}
    (run : call.selectedRun = (created, accounts, gas, substate, true, output)) :
    ∃ locals label, CallBound call.entryState locals label := by
  rw [message_selected_runtime call keys ready ordinary] at run
  have execution := (message_call_accepted call runtimeBytecode created accounts gas substate output run).1
  exact runtime_success_call_bound rfl bounded execution

/-- A successful message identifies its mapping keys from actual calldata. -/
theorem message_accepted_scoped_binding (call : MessageCall) (keys : AccessScope)
    (ready : BoundaryReady call.receiver call.accounts keys)
    (ordinary : call.receiver ∉ π) (bounded : call.calldata.size < UInt256.size)
    {created accounts gas substate output}
    (run : call.selectedRun = (created, accounts, gas, substate, true, output)) :
    ∃ locals label, CallBound call.entryState locals label ∧
      entryKeys label.entry = calldataScope call.entryState.executionEnv := by
  rw [message_selected_runtime call keys ready ordinary] at run
  have execution := (message_call_accepted call runtimeBytecode created accounts gas substate output run).1
  exact runtime_success_scoped_binding rfl bounded execution

/-- Successful messages refine the model without a supplied call label. -/
theorem message_accepted_refines_model (call : MessageCall) (keys : AccessScope)
    (ready : BoundaryReady call.receiver call.accounts keys)
    (safe : Safe (boundaryModel call.receiver call.accounts keys))
    (ordinary : call.receiver ∉ π) (different : call.receiver ≠ call.sender)
    (value : call.contextValue = call.value)
    (funds : call.value.toNat ≤ ethLedger call.accounts call.sender)
    (bounded : call.calldata.size < UInt256.size)
    (covered : CalldataCovered call.entryState keys)
    {created accounts gas substate output}
    (run : call.selectedRun = (created, accounts, gas, substate, true, output)) :
    BoundaryReady call.receiver accounts keys ∧ Safe (boundaryModel call.receiver accounts keys) ∧
      ∃ locals label result payments,
        CallBound call.entryState locals label ∧
        CallStep (boundaryModel call.receiver call.accounts keys) label (.success result) payments
          (boundaryModel call.receiver accounts keys) ∧
        returnDataEquiv output (returnValues result) (.abi (entryTransition label.entry).returnType) := by
  obtain ⟨locals, label, bound, scope⟩ := message_accepted_scoped_binding call keys ready ordinary bounded run
  have accesses : entryKeys label.entry ⊆ keys := by
    rw [scope]
    exact covered
  obtain ⟨nextReady, result, payments, step, returned⟩ := message_refines_model call locals label keys
    ready safe ordinary different value funds bounded bound accesses run
  exact ⟨nextReady, callStep_safe safe step, locals, label, result, payments, bound, step, returned⟩

end Rollup.EVM
