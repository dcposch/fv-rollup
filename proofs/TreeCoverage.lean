import semantics.TreeCoverage
import proofs.ExecutionTree
import Ethereum.Theory.ProgressLemmas

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- A root frame's collected keys cover its calldata. -/
theorem frame_calldata_covered {self : Address} {state : Ethereum.State} {keys : AccessScope}
    (owner : state.executionEnv.codeOwner = self) (subset : frameCalldataScope self state ⊆ keys) :
    CalldataCovered state keys := by
  simpa only [frameCalldataScope, owner, if_true, CalldataCovered] using subset

/-- The collected scope covers every root frame, including descendants of reverted calls. -/
theorem frame_run_covered_of_scope {fuel jumps start result} (run : FrameRun fuel jumps start result) :
    ∀ self keys, run.scope self ⊆ keys → run.covered self keys := by
  refine FrameRun.rec
    (motive_1 := fun _ _ _ _ run => ∀ self keys, run.scope self ⊆ keys → run.covered self keys)
    (motive_2 := fun _ _ children => ∀ self keys,
      children.scope self ⊆ keys → children.covered self keys)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ run
  · intro jumps start self keys subset
    exact ⟨fun owner => frame_calldata_covered owner
      (Finset.Subset.trans Finset.subset_union_left subset), trivial⟩
  · intro fuel jumps start error children executed ih self keys subset
    exact ⟨fun owner => frame_calldata_covered owner
      (Finset.Subset.trans Finset.subset_union_left subset),
      ih self keys (Finset.Subset.trans Finset.subset_union_right subset)⟩
  · intro fuel jumps start after output children executed ih self keys subset
    exact ⟨fun owner => frame_calldata_covered owner
      (Finset.Subset.trans Finset.subset_union_left subset),
      ih self keys (Finset.Subset.trans Finset.subset_union_right subset)⟩
  · intro fuel jumps start after output children executed ih self keys subset
    exact ⟨fun owner => frame_calldata_covered owner
      (Finset.Subset.trans Finset.subset_union_left subset),
      ih self keys (Finset.Subset.trans Finset.subset_union_right subset)⟩
  · intro fuel jumps start after result children executed rest childIH restIH self keys subset
    refine ⟨fun owner => frame_calldata_covered owner
      (Finset.Subset.trans Finset.subset_union_left subset), ?_, ?_⟩
    · exact childIH self keys (Finset.Subset.trans Finset.subset_union_left
        (Finset.Subset.trans Finset.subset_union_right subset))
    · apply restIH self keys
      have environment := Xstep_env_unchanged start after jumps none executed
      have same : frameCalldataScope self { after with executionEnv.depth := start.executionEnv.depth } =
          frameCalldataScope self start := by
        simp only [frameCalldataScope, ← environment]
      change frameCalldataScope self { after with executionEnv.depth := start.executionEnv.depth } ∪
        rest.nestedScope self ⊆ _
      rw [same]
      exact Finset.union_subset
        (Finset.Subset.trans Finset.subset_union_left subset)
        (Finset.Subset.trans Finset.subset_union_right
          (Finset.Subset.trans Finset.subset_union_right subset))
  · intro jumps start noCall noCreation self keys subset
    trivial
  · intro jumps start child result entered run ih self keys subset
    exact ih self keys subset
  · intro jumps start child result entered run ih self keys subset
    exact ih self keys subset

/-- Each recorded tree supplies its own complete finite calldata scope. -/
theorem frame_run_scope_covered {fuel jumps start result} (run : FrameRun fuel jumps start result)
    (self : Address) : run.covered self (run.scope self) :=
  frame_run_covered_of_scope run self _ (Finset.Subset.refl _)

end Rollup.EVM
