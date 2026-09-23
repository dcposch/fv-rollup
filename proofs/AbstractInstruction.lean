import proofs.AbstractSimulation
import proofs.AbstractCursor
import proofs.InstructionContinue

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- A continuing EVM instruction stays within the abstract successors. -/
theorem abstract_instruction_sound {cursor : AbstractCursor} {next : List AbstractCursor}
    {before after : Ethereum.State} {jumps : Array UInt256}
    (represented : cursor.denotes before) (locked : (before.sload ⟨6⟩).2 ≠ ⟨0⟩)
    (advance : cursor.successors ((decode before.executionEnv.code cursor.pc).getD (.STOP, none)).1
      ((decode before.executionEnv.code cursor.pc).getD (.STOP, none)).2 = some next)
    (run : Xstep jumps before = .ok (after, none)) :
    ∃ following ∈ next, following.denotes after := by
  let instruction := (decode before.executionEnv.code cursor.pc).getD (.STOP, none)
  have decoded : (decode before.executionEnv.code before.machineState.pc).getD (.STOP, none) =
      (instruction.1, instruction.2) := by rw [represented.1]
  obtain ⟨checked, cost, stepped, precheck, opcode, result⟩ := instruction_state_step decoded run
  have checkedRepresented := abstract_cursor_precheck represented precheck
  have checkedLocked : (checked.sload ⟨6⟩).2 ≠ ⟨0⟩ := by
    simpa only [Ethereum.State.sload, Ethereum.State.lookupAccount,
      precheck_accounts precheck, Z_executionEnv_eq precheck] using locked
  have successors := abstract_step_sound
    (before := { checked with executionEnv.depth := before.executionEnv.depth })
    checkedRepresented checkedLocked (continuing_instruction_kind decoded run) advance opcode
  obtain ⟨following, member, known⟩ := successors
  refine ⟨following, member, ?_⟩
  rw [result]
  exact known

end Rollup.EVM
