import proofs.support.TraceScope

namespace Rollup.EVM

theorem event_covered_iff_keys (event : ExecutionEvent) (keys : AccessScope) :
    event.covered keys ↔ event.keys ⊆ keys := by
  cases event with
  | message => rfl
  | donation => simp [ExecutionEvent.covered, ExecutionEvent.keys]
  | selfdestruct => simp [ExecutionEvent.covered, ExecutionEvent.keys]
  | rejected => simp [ExecutionEvent.covered, ExecutionEvent.keys]

theorem execution_scope_fixed (events : List ExecutionEvent) : fixedKeys ⊆ executionScope events := by
  induction events with
  | nil => exact Finset.Subset.refl _
  | cons event events ih => exact Finset.Subset.trans ih Finset.subset_union_right

/-- The collected finite set covers every root message in the trace. -/
theorem execution_scope_covered (events : List ExecutionEvent) :
    ∀ event ∈ events, event.covered (executionScope events) := by
  induction events with
  | nil => simp
  | cons head tail ih =>
    intro event member
    rw [event_covered_iff_keys]
    rcases List.mem_cons.mp member with same | old
    · subst event
      exact Finset.subset_union_left
    · exact Finset.Subset.trans ((event_covered_iff_keys event _).mp (ih event old))
        Finset.subset_union_right

end Rollup.EVM
