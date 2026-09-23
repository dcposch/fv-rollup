import proofs.RootEntryPath
import proofs.CreationPrefixBoundary

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- Actual call and creation paths carry the proved boundary to the root invocation. -/
theorem root_entry_boundary {self keys root start}
    (path : CoveredRootEntryPath self keys root start) (ordinary : self ∉ π)
    (ready : BoundaryReady self start.accountMap keys) (safe : Safe (boundaryModel self start.accountMap keys)) :
    BoundaryRefines self keys start.accountMap root.accountMap := by
  induction path with
  | here owner code covered => exact ⟨ready, safe, .initial⟩
  | call foreign earlier entered rest ih =>
    have first := continuing_prefix_boundary earlier ordinary foreign ready safe
    have environment := continuing_prefix_environment (covered_prefix_execution earlier)
    have beforeForeign := ne_of_ne_of_eq foreign (congrArg ExecutionEnv.codeOwner environment).symm
    have next := child_call_entry_boundary entered beforeForeign first.1 first.2.1
    exact boundary_refines_trans first (boundary_refines_trans next (ih next.1 next.2.1))
  | creation foreign earlier entered rest ih =>
    have first := continuing_prefix_boundary earlier ordinary foreign ready safe
    have environment := continuing_prefix_environment (covered_prefix_execution earlier)
    have beforeForeign := ne_of_ne_of_eq foreign (congrArg ExecutionEnv.codeOwner environment).symm
    rcases child_creation_entry_boundary entered beforeForeign first.1 first.2.1 with
      ⟨invalid, zero⟩ | ⟨_, next⟩
    · exact False.elim (root_entry_invalid (covered_root_entry_execution rest) invalid zero)
    · exact boundary_refines_trans first (boundary_refines_trans next (ih next.1 next.2.1))

/-- A reached root frame has the code, storage, world, and solvency conditions for its proofs. -/
theorem root_entry_ready {self keys root start}
    (path : CoveredRootEntryPath self keys root start) (ordinary : self ∉ π)
    (ready : BoundaryReady self start.accountMap keys) (safe : Safe (boundaryModel self start.accountMap keys)) :
    OwnCode root ∧ WorldBounded root ∧ StorageReady root root.executionEnv.codeOwner keys ∧
      Safe (project root root.executionEnv.codeOwner keys) ∧ CalldataCovered root keys := by
  have reached := root_entry_boundary path ordinary ready safe
  obtain ⟨owner, code, covered⟩ := root_entry_binding path
  refine ⟨⟨code, ?_⟩, reached.1.2.1, ?_, ?_, covered⟩
  · change (root.accountMap.find? root.executionEnv.codeOwner).map (·.code) = some runtimeBytecode
    rw [owner]
    exact reached.1.1.2
  · rw [owner]
    exact reached.1.2.2.1
  · rw [owner, project_boundary]
    exact reached.2.1

end Rollup.EVM
