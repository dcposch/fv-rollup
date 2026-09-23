import semantics.PrefixCoverage
import proofs.CallbackPrefix
import proofs.TreeBoundary
import proofs.TreeCoverage

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- Complete child records have the proved boundary effect. -/
theorem instruction_children_refine {jumps state} (children : InstructionChildren jumps state)
    (self : Address) (keys : AccessScope) (ordinary : self ∉ π)
    (covered : children.covered self keys) : children.refines self keys := by
  cases children with
  | none noCall noCreation => trivial
  | call entered run =>
    exact fun foreign ready safe => frame_run_boundary run self keys ordinary foreign ready safe covered
  | creation entered run =>
    exact fun foreign ready safe => frame_run_boundary run self keys ordinary foreign ready safe covered

/-- A child's collected scope covers its nested execution. -/
theorem instruction_children_covered_of_scope {jumps state}
    (children : InstructionChildren jumps state) (self : Address) (keys : AccessScope)
    (scope : children.scope self ⊆ keys) : children.covered self keys := by
  cases children with
  | none noCall noCreation => trivial
  | call entered run => exact frame_run_covered_of_scope run self keys scope
  | creation entered run => exact frame_run_covered_of_scope run self keys scope

/-- Coverage retains the actual continuing instruction prefix. -/
theorem covered_prefix_execution {self keys jumps start current}
    (trace : CoveredPrefix self keys jumps start current) : ContinuingPrefix jumps start current := by
  induction trace with
  | initial => exact .initial
  | next earlier scope run ih => exact .next ih run

/-- Increasing a prefix scope retains coverage. -/
theorem prefix_covered_mono {self keys jumps start current}
    (trace : CoveredPrefix self keys jumps start current) {larger : AccessScope}
    (subset : keys ⊆ larger) : CoveredPrefix self larger jumps start current := by
  induction trace with
  | initial => exact .initial
  | next earlier scope run ih => exact .next ih (Finset.Subset.trans scope subset) run

/-- Every finite instruction prefix has a finite scope from its actual child records. -/
theorem prefix_has_scope {jumps start current} (trace : ContinuingPrefix jumps start current)
    (self : Address) : ∃ keys, CoveredPrefix self keys jumps start current := by
  induction trace with
  | initial => exact ⟨∅, .initial⟩
  | @next before after earlier run ih =>
    obtain ⟨keys, covered⟩ := ih
    exact ⟨keys ∪ (instructionRecord jumps before).scope self,
      .next (prefix_covered_mono covered Finset.subset_union_left) Finset.subset_union_right run⟩

/-- Continuing foreign execution preserves the rollup at each instruction boundary. -/
theorem continuing_prefix_boundary {self keys jumps start current}
    (trace : CoveredPrefix self keys jumps start current)
    (ordinary : self ∉ π) (foreign : self ≠ start.executionEnv.codeOwner)
    (ready : BoundaryReady self start.accountMap keys) (safe : Safe (boundaryModel self start.accountMap keys)) :
    BoundaryRefines self keys start.accountMap current.accountMap := by
  induction trace with
  | initial => exact ⟨ready, safe, .initial⟩
  | @next before after earlier scope run ih =>
    have environment := continuing_prefix_environment (covered_prefix_execution earlier)
    have different : self ≠ before.executionEnv.codeOwner := by rwa [environment]
    let children := instructionRecord jumps before
    have coverage := instruction_children_covered_of_scope children self keys scope
    have last := instruction_tree_refines children ordinary different ih.1 ih.2.1 coverage
      (instruction_children_refine children self keys ordinary coverage) run
    exact boundary_refines_trans ih last

end Rollup.EVM
