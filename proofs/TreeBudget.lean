import proofs.InstructionBudget
import proofs.TreeBoundary

open Ethereum Ethereum.EVM

namespace Rollup.EVM

private theorem children_boundary (children : InstructionChildren jumps start)
    (self : Address) (keys : AccessScope) (ordinary : self ∉ π)
    (covered : children.covered self keys) : children.refines self keys := by
  cases children with
  | none noCall noCreation => trivial
  | call entered run =>
    exact fun foreign ready safe => frame_run_boundary run self keys ordinary foreign ready safe covered
  | creation entered run =>
    exact fun foreign ready safe => frame_run_boundary run self keys ordinary foreign ready safe covered

/-- Complete foreign frames preserve total ETH, including nested rollup calls and creation. -/
theorem frame_run_budget {fuel jumps start result} (run : FrameRun fuel jumps start result) :
    ∀ self keys, self ∉ π → self ≠ start.executionEnv.codeOwner →
      BoundaryReady self start.accountMap keys → Safe (boundaryModel self start.accountMap keys) →
      run.covered self keys → FrameResultBudget start.accountMap result := by
  refine FrameRun.rec
    (motive_1 := fun _ _ start result run =>
      ∀ self keys, self ∉ π → self ≠ start.executionEnv.codeOwner →
        BoundaryReady self start.accountMap keys → Safe (boundaryModel self start.accountMap keys) →
        run.covered self keys → FrameResultBudget start.accountMap result)
    (motive_2 := fun _ _ children => ∀ self keys, self ∉ π →
      children.covered self keys → children.budget self keys)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ run
  · intro jumps start self keys ordinary foreign ready safe covered
    trivial
  · intro fuel jumps start error children executed ih self keys ordinary foreign ready safe covered
    trivial
  · intro fuel jumps start after output children executed ih self keys ordinary foreign ready safe covered
    exact instruction_tree_budget children ordinary foreign ready safe covered.2
      (ih self keys ordinary covered.2) executed
  · intro fuel jumps start after output children executed ih self keys ordinary foreign ready safe covered
    trivial
  · intro fuel jumps start after result children executed rest childIH restIH
      self keys ordinary foreign ready safe covered
    have first := instruction_tree_budget children ordinary foreign ready safe covered.2.1
      (childIH self keys ordinary covered.2.1) executed
    have conditions := instruction_tree_refines children ordinary foreign ready safe covered.2.1
      (children_boundary children self keys ordinary covered.2.1) executed
    have environment := Xstep_env_unchanged start after jumps none executed
    have restForeign : self ≠ ({ after with executionEnv.depth := start.executionEnv.depth } : Ethereum.State).executionEnv.codeOwner := by
      simpa only [← environment] using foreign
    have last := restIH self keys ordinary restForeign conditions.1 conditions.2.1 covered.2.2
    cases result with
    | error error => trivial
    | ok outcome =>
      cases outcome with
      | revert gas data => trivial
      | success state data => exact last.trans first
  · intro jumps start noCall noCreation self keys ordinary covered
    trivial
  · intro jumps start child result entered run ih self keys ordinary covered
    exact fun foreign ready safe => ih self keys ordinary foreign ready safe covered
  · intro jumps start child result entered run ih self keys ordinary covered
    exact fun foreign ready safe => ih self keys ordinary foreign ready safe covered

end Rollup.EVM
