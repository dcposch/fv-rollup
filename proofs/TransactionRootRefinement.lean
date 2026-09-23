import proofs.TransactionRootMessage

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- Every reached root message has exact labeled effects or account and substate rollback. -/
theorem transaction_root_message_refined {event start root self keys}
    (entry : TransactionCodeEntry event start) (path : CoveredRootEntryPath self keys root start)
    (admissible : event.admissible self) (ordinary : self ∉ π)
    (ready : BoundaryReady self event.before keys) (safe : Safe (boundaryModel self event.before keys)) :
    ∃ call : MessageCall,
      root = call.codeEntry runtimeBytecode ∧ MessageEnvironment self call ∧
      ∀ result : MessageResult, call.selectedRun = result.tuple →
        BoundaryRefines self keys call.accounts result.accounts ∧
          (ExecutionEvent.message call result).refined keys := by
  obtain ⟨call, bound, environment, beforeReady, beforeSafe⟩ :=
    transaction_root_message_origin entry path admissible ordinary ready safe
  have covered := (root_entry_binding path).2.2
  have callCovered : CalldataCovered call.entryState keys := by
    rw [bound] at covered
    exact covered
  refine ⟨call, bound, environment, ?_⟩
  intro result executed
  have refined := execution_step_refines ordinary beforeReady beforeSafe
    (.message call result environment executed) callCovered
  exact ⟨⟨refined.1, refined.2.1, refined.2.2.1⟩, refined.2.2.2⟩

end Rollup.EVM
