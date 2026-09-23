import proofs.support.ExecutionBudget
import proofs.ChildEntryUnique
import proofs.ExecutionTree

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- Child uniqueness binds the budget induction hypothesis to actual execution. -/
theorem recorded_child_frames_budget {jumps : Array UInt256} {before : Ethereum.State}
    (children : InstructionChildren jumps before) {self : Address} {keys : AccessScope}
    (refined : children.budget self keys) : ChildFramesBudget self keys jumps before := by
  intro child entry foreign ready safe
  cases children with
  | none noCall noCreation =>
    rcases entry with call | creation
    · exact (noCall child call).elim
    · exact (noCreation child creation).elim
  | call actual run =>
    rcases entry with call | creation
    · have same := child_call_entry_unique actual call
      subst child
      rw [frame_run_sound run]
      exact refined foreign ready safe
    · exact (child_entries_exclusive actual creation).elim
  | creation actual run =>
    rcases entry with call | creation
    · exact (child_entries_exclusive call actual).elim
    · have same := child_creation_entry_unique actual creation
      subst child
      rw [frame_run_sound run]
      exact refined foreign ready safe

end Rollup.EVM
