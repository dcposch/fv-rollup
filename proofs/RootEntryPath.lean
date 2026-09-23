import semantics.RootEntryPath
import proofs.PrefixBoundary
import proofs.ActiveFailure
import proofs.FreshFrame

open Ethereum Ethereum.EVM Reasoning.Theory

namespace Rollup.EVM

/-- Coverage does not change the underlying execution path. -/
theorem covered_root_entry_execution {self keys root start}
    (path : CoveredRootEntryPath self keys root start) : RootEntryPath self root start := by
  induction path with
  | here owner code covered => exact .here owner code
  | call foreign earlier entered rest ih => exact .call foreign (covered_prefix_execution earlier) entered ih
  | creation foreign earlier entered rest ih => exact .creation foreign (covered_prefix_execution earlier) entered ih

/-- Increasing the finite key set retains path coverage. -/
theorem root_entry_covered_mono {self keys root start} (path : CoveredRootEntryPath self keys root start)
    {larger : AccessScope} (subset : keys ⊆ larger) : CoveredRootEntryPath self larger root start := by
  induction path with
  | here owner code covered => exact .here owner code (Finset.Subset.trans covered subset)
  | call foreign earlier entered rest ih => exact .call foreign (prefix_covered_mono earlier subset) entered ih
  | creation foreign earlier entered rest ih => exact .creation foreign (prefix_covered_mono earlier subset) entered ih

/-- Every actual finite path has a finite scope collected from its executed frames. -/
theorem root_entry_has_scope {self root start} (path : RootEntryPath self root start) :
    ∃ keys, CoveredRootEntryPath self keys root start := by
  induction path with
  | here owner code => exact ⟨calldataScope root.executionEnv, .here owner code (Finset.Subset.refl _)⟩
  | call foreign earlier entered rest ih =>
    obtain ⟨prefixKeys, first⟩ := prefix_has_scope earlier self
    obtain ⟨childKeys, next⟩ := ih
    exact ⟨prefixKeys ∪ childKeys, .call foreign
      (prefix_covered_mono first Finset.subset_union_left) entered
      (root_entry_covered_mono next Finset.subset_union_right)⟩
  | creation foreign earlier entered rest ih =>
    obtain ⟨prefixKeys, first⟩ := prefix_has_scope earlier self
    obtain ⟨childKeys, next⟩ := ih
    exact ⟨prefixKeys ∪ childKeys, .creation foreign
      (prefix_covered_mono first Finset.subset_union_left) entered
      (root_entry_covered_mono next Finset.subset_union_right)⟩

/-- An invalid creation stub cannot lead to an invocation of the rollup code. -/
theorem root_entry_invalid {self root start} (path : RootEntryPath self root start)
    (code : start.executionEnv.code = ⟨#[0xfe]⟩) (counter : start.machineState.pc = ⟨0⟩) : False := by
  have failed := invalid_entry_error start (D_J start.executionEnv.code 0) code counter
  have decoded : decode start.executionEnv.code start.machineState.pc = some (.INVALID, none) := by
    rw [code, counter]
    decide +kernel
  cases path with
  | here owner pinned =>
    have sizes := congrArg ByteArray.size (code.symm.trans pinned)
    have different : (⟨#[0xfe]⟩ : ByteArray).size ≠ runtimeBytecode.size := by decide +kernel
    exact different sizes
  | call foreign earlier entered rest =>
    have same := continuing_prefix_entry_error failed earlier
    subst_vars
    cases entered with
    | entered instruction precheck arguments enabled selected =>
      simp only [decoded, Option.getD_some, Prod.mk.injEq] at instruction
      rcases instruction with ⟨rfl, rfl⟩
      simp [Z, δ] at precheck
  | creation foreign earlier entered rest =>
    have same := continuing_prefix_entry_error failed earlier
    subst_vars
    cases entered with
    | entered instruction precheck arguments bounded allowed =>
      simp only [decoded, Option.getD_some, Prod.mk.injEq] at instruction
      rcases instruction with ⟨rfl, rfl⟩
      simp [Z, δ] at precheck

/-- Root entries on these paths have the interpreter's fresh-frame shape. -/
theorem root_entry_fresh {self root start} (path : RootEntryPath self root start)
    (fresh : FreshFrame start) : FreshFrame root := by
  induction path with
  | here => exact fresh
  | call foreign earlier entered rest ih => exact ih (child_call_entry_fresh entered)
  | creation foreign earlier entered rest ih => exact ih (child_creation_entry_fresh entered)

/-- Calldata stays word bounded on every call or creation path. -/
theorem root_entry_bounded {self root start} (path : RootEntryPath self root start)
    (bounded : start.executionEnv.calldata.size < UInt256.size) :
    root.executionEnv.calldata.size < UInt256.size := by
  induction path with
  | here => exact bounded
  | call foreign earlier entered rest ih => exact ih (child_call_entry_bounded entered)
  | creation foreign earlier entered rest ih => exact ih (child_creation_entry_bounded entered)

/-- A covered path includes the actual root code, context, and calldata keys. -/
theorem root_entry_binding {self keys root start} (path : CoveredRootEntryPath self keys root start) :
    root.executionEnv.codeOwner = self ∧ root.executionEnv.code = runtimeBytecode ∧ CalldataCovered root keys := by
  induction path with
  | here owner code covered => exact ⟨owner, code, covered⟩
  | call foreign earlier entered rest ih => exact ih
  | creation foreign earlier entered rest ih => exact ih

end Rollup.EVM
