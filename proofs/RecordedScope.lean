import semantics.recording.ExecutionTreeComplete
import proofs.TreeCoverage

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- Any actual finite execution result has a complete instruction and child-call record. -/
theorem execution_has_tree {fuel : Nat} {jumps : Array UInt256} {start : Ethereum.State}
    {result : Except ExecutionException (ExecutionResult Ethereum.State)}
    (executed : X fuel jumps start = result) : Nonempty (FrameRun fuel jumps start result) := by
  rw [← executed]
  exact frame_run_complete fuel jumps start

/-- Actual execution supplies a finite scope for all nested root calldata and fixed slots. -/
theorem execution_has_covered_tree (self : Address) {fuel : Nat} {jumps : Array UInt256}
    {start : Ethereum.State} {result : Except ExecutionException (ExecutionResult Ethereum.State)}
    (executed : X fuel jumps start = result) :
    ∃ run : FrameRun fuel jumps start result, run.covered self (fixedKeys ∪ run.scope self) := by
  obtain ⟨run⟩ := execution_has_tree executed
  exact ⟨run, frame_run_covered_of_scope run self _ Finset.subset_union_right⟩

end Rollup.EVM
