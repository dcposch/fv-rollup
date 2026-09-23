import semantics.ExecutionTree

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- Each recorded frame has exactly the result of the pinned EVM execution function. -/
theorem frame_run_sound {fuel jumps start result} (run : FrameRun fuel jumps start result) :
    X fuel jumps start = result := by
  induction fuel generalizing jumps start result with
  | zero => cases run; simp only [X]
  | succ fuel ih =>
    cases run with
    | failed children executed => simp only [X, executed, bind, Except.bind]
    | returned children executed => simp only [X, executed, bind, Except.bind]
    | reverted children executed => simp only [X, executed, bind, Except.bind]
    | continued children executed rest =>
      simp only [X, executed, bind, Except.bind]
      exact ih rest

/-- The recorded scope contains every mapping key selected by a root frame's calldata. -/
theorem frame_run_entry_covered {fuel jumps start result} (run : FrameRun fuel jumps start result)
    {self : Address} (owner : start.executionEnv.codeOwner = self) :
    CalldataCovered start (run.scope self) := by
  change calldataScope start.executionEnv ⊆ frameCalldataScope self start ∪ run.nestedScope self
  simp only [frameCalldataScope, owner, if_true]
  exact Finset.subset_union_left

end Rollup.EVM
