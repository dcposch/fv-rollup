import semantics.TreeCoverage
import proofs.ChildEntryUnique

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- The recorded children cover any actual message entry in the rollup context. -/
theorem child_call_calldata_covered {jumps : Array UInt256} {start child : Ethereum.State}
    (children : InstructionChildren jumps start) {self : Address} {keys : AccessScope}
    (covered : children.covered self keys) (entered : ChildCallEntry jumps start child)
    (owner : child.executionEnv.codeOwner = self) : CalldataCovered child keys := by
  cases children with
  | none noCall noCreation => exact (noCall child entered).elim
  | call actual run =>
    have same := child_call_entry_unique actual entered
    subst child
    cases run <;> exact covered.1 owner
  | creation actual run => exact (child_entries_exclusive entered actual).elim

/-- The recorded children cover any actual initialization entry in the rollup context. -/
theorem child_creation_calldata_covered {jumps : Array UInt256} {start child : Ethereum.State}
    (children : InstructionChildren jumps start) {self : Address} {keys : AccessScope}
    (covered : children.covered self keys) (entered : ChildCreationEntry jumps start child)
    (owner : child.executionEnv.codeOwner = self) : CalldataCovered child keys := by
  cases children with
  | none noCall noCreation => exact (noCreation child entered).elim
  | call actual run => exact (child_entries_exclusive actual entered).elim
  | creation actual run =>
    have same := child_creation_entry_unique actual entered
    subst child
    cases run <;> exact covered.1 owner

end Rollup.EVM
