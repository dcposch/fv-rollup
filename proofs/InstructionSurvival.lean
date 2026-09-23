import proofs.CallInstructionSurvival
import proofs.CreationInstructionSurvival
import proofs.InstructionTree

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- Each instruction preserves account survival when its recorded children do. -/
theorem instruction_tree_survives {before after : Ethereum.State} {jumps : Array UInt256} {ret}
    {self : Address} (children : InstructionChildren jumps before)
    (initial : StateSurvives self before) (survived : children.survives self)
    (run : Xstep jumps before = .ok (after, ret)) : StateSurvives self after := by
  rcases decoded : (decode before.executionEnv.code before.machineState.pc).getD (.STOP, none) with ⟨op, arg⟩
  by_cases internal : LocalOperation op
  · exact local_instruction_survives initial internal decoded run
  · have frames := recorded_child_frames_survive children survived
    rcases nonlocal_operation_cases internal with calls | creations | rfl
    · exact call_instruction_survives initial decoded calls frames run
    · exact creation_instruction_survives initial decoded creations frames run
    · exact selfdestruct_instruction_survives initial decoded run

end Rollup.EVM
