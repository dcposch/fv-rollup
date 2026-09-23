import invariants.ExecutionTrace
import semantics.ExecutionTrace
import proofs.MessageClassification
import proofs.BoundaryDonation
import proofs.DestructionBoundary
import proofs.MessageRollback

open Ethereum Ethereum.EVM Solm Reasoning.Theory

namespace Rollup

theorem callTrace_trans {start middle after : State}
    (left : CallTrace start middle) (right : CallTrace middle after) : CallTrace start after := by
  induction right with
  | initial => exact left
  | next _ step ih => exact .next ih step

namespace EVM

/-- One actual EVM event preserves safety and has a model trace and exact message result. -/
theorem execution_step_refines {self before after event keys}
    (ordinary : self ∉ π) (ready : BoundaryReady self before keys)
    (safe : Safe (boundaryModel self before keys))
    (step : ExecutionStep self event before after) (covered : event.covered keys) :
    BoundaryReady self after keys ∧ Safe (boundaryModel self after keys) ∧
      CallTrace (boundaryModel self before keys) (boundaryModel self after keys) ∧ event.refined keys := by
  cases step with
  | message call result environment executed =>
    rcases environment with ⟨rfl, different, value, funds, bounded⟩
    rcases result with ⟨created, accounts, gas, substate, accepted, output⟩
    cases accepted with
    | true =>
      obtain ⟨nextReady, nextSafe, locals, label, result, payments, bound, effect, returned⟩ :=
        message_accepted_refines_model call keys ready safe ordinary different value funds bounded covered executed
      exact ⟨nextReady, nextSafe, .next .initial (.call effect),
        locals, label, result, payments, bound, effect, returned⟩
    | false =>
      obtain ⟨same, restored⟩ := message_rejected_boundary call keys ready ordinary executed
      refine ⟨same.symm ▸ ready, same.symm ▸ safe, ?_, same, restored⟩
      rw [same]
      exact .initial
  | donation _ sender value different funds =>
    obtain ⟨nextReady, model, bound⟩ := boundary_donation self sender before value keys ready different funds
    have effect : TraceStep (boundaryModel self before keys)
        (boundaryModel self (sendEth self sender value true before) keys) := by
      rw [model]
      exact .donation bound
    have trace := CallTrace.next CallTrace.initial effect
    exact ⟨nextReady, callTrace_safe safe trace, trace, trivial⟩
  | selfdestruct different decoded executed =>
    obtain ⟨nextReady, nextSafe, trace⟩ :=
      selfdestruct_instruction_refines different ready safe decoded executed
    exact ⟨nextReady, nextSafe, trace, trivial⟩
  | rejected call result rejected executed =>
    rcases result with ⟨created, accounts, gas, substate, accepted, output⟩
    dsimp only at rejected
    subst accepted
    obtain ⟨same, restored⟩ := theta_rejected_checkpoint executed
    refine ⟨same.symm ▸ ready, same.symm ▸ safe, ?_, same, restored⟩
    rw [same]
    exact .initial

/-- Finite EVM execution preserves all boundary conditions and exact committed call effects. -/
theorem completed_trace_correct : CompletedTraceCorrect := by
  intro self start events after keys ordinary ready safe trace covered
  induction trace with
  | initial => exact ⟨ready, safe, .initial, by simp⟩
  | @next events before after event trace step ih =>
    have previous : ∀ e ∈ events, ExecutionEvent.covered e keys := by
      intro e member
      exact covered e (List.mem_append_left _ member)
    have current : event.covered keys := covered event (by simp)
    obtain ⟨beforeReady, beforeSafe, earlier, earlierResults⟩ := ih previous
    obtain ⟨afterReady, afterSafe, next, result⟩ :=
      execution_step_refines ordinary beforeReady beforeSafe step current
    refine ⟨afterReady, afterSafe, callTrace_trans earlier next, ?_⟩
    intro e member
    rcases List.mem_append.mp member with old | last
    · exact earlierResults e old
    · have same : e = event := by simpa using last
      exact same ▸ result

/-- Committed EVM traces keep all credit backed by ETH at each final boundary. -/
theorem completed_trace_custody {self start events after keys}
    (ordinary : self ∉ π) (ready : BoundaryReady self start keys)
    (safe : Safe (boundaryModel self start keys))
    (trace : ExecutionTrace self start events after) (covered : ∀ event ∈ events, event.covered keys) :
    liabilities (boundaryModel self after keys) ≤ (boundaryModel self after keys).eth := by
  have solvent := (completed_trace_correct self start events after keys ordinary ready safe trace covered).2.1.1
  have idle : (boundaryModel self after keys).payment = none := rfl
  simpa only [Solvent, reserved, idle, Option.map_none, Option.getD_none, Nat.add_zero] using solvent

/-- Every stored model value remains word-sized over actual EVM traces. -/
theorem completed_trace_word_bounds {self start events after keys}
    (ordinary : self ∉ π) (ready : BoundaryReady self start keys)
    (safe : Safe (boundaryModel self start keys))
    (trace : ExecutionTrace self start events after) (covered : ∀ event ∈ events, event.covered keys) :
    WordBounded (boundaryModel self after keys) :=
  (completed_trace_correct self start events after keys ordinary ready safe trace covered).2.1.2.2

end EVM
end Rollup
