import proofs.support.ChildSurvival
import proofs.ChildEntryUnique
import proofs.ExecutionTree

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- Child uniqueness binds the survival induction hypothesis to actual execution. -/
theorem recorded_child_frames_survive {jumps : Array UInt256} {before : Ethereum.State}
    (children : InstructionChildren jumps before) {self : Address}
    (refined : children.survives self) : ChildFramesSurvive self jumps before := by
  intro child entry initial
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
      exact refined initial
    · exact (child_entries_exclusive actual creation).elim
  | creation actual run =>
    rcases entry with call | creation
    · exact (child_entries_exclusive call actual).elim
    · have same := child_creation_entry_unique actual creation
      subst child
      rw [frame_run_sound run]
      exact refined initial

end Rollup.EVM
