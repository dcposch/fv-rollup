import proofs.DestructionLocal
import proofs.InstructionState
import proofs.RuntimeDestruction
import proofs.AddressOrder

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- Validation and a local instruction preserve pending account deletions. -/
theorem local_instruction_destruct_set {before after : Ethereum.State} {jumps : Array UInt256}
    {op : Operation} {arg : Option (UInt256 × Nat)} {ret}
    (internal : LocalOperation op)
    (decoded : (decode before.executionEnv.code before.machineState.pc).getD (.STOP, none) = (op, arg))
    (run : Xstep jumps before = .ok (after, ret)) :
    after.substate.selfDestructSet = before.substate.selfDestructSet := by
  obtain ⟨checked, cost, stepped, precheck, opcode, same⟩ := instruction_state_step decoded run
  rw [same]
  have unchanged : stepped.substate.selfDestructSet = checked.substate.selfDestructSet :=
    local_step_destruct_set
      (before := { checked with executionEnv.depth := before.executionEnv.depth }) internal opcode
  exact unchanged.trans (precheck_destruct_set precheck)

/-- A self-destruct instruction can add only its current code owner to pending deletions. -/
theorem selfdestruct_instruction_set {before after : Ethereum.State} {jumps : Array UInt256}
    {arg : Option (UInt256 × Nat)} {ret}
    (decoded : (decode before.executionEnv.code before.machineState.pc).getD (.STOP, none) = (.SELFDESTRUCT, arg))
    (run : Xstep jumps before = .ok (after, ret)) :
    after.substate.selfDestructSet = before.substate.selfDestructSet ∨
      after.substate.selfDestructSet = before.substate.selfDestructSet.insert before.executionEnv.codeOwner := by
  obtain ⟨checked, cost, stepped, precheck, opcode, same⟩ := instruction_state_step decoded run
  have unchanged := precheck_destruct_set precheck
  have environment := Z_executionEnv_eq precheck
  have result := selfdestruct_step_set opcode
  simpa only [same, unchanged, environment] using result

/-- Deleting a foreign executing account cannot schedule the rollup for deletion. -/
theorem foreign_selfdestruct_excludes_rollup {before after : Ethereum.State} {jumps : Array UInt256}
    {arg : Option (UInt256 × Nat)} {ret} {self : Address}
    (foreign : self ≠ before.executionEnv.codeOwner)
    (absent : self ∉ before.substate.selfDestructSet)
    (decoded : (decode before.executionEnv.code before.machineState.pc).getD (.STOP, none) = (.SELFDESTRUCT, arg))
    (run : Xstep jumps before = .ok (after, ret)) :
    self ∉ after.substate.selfDestructSet := by
  rcases selfdestruct_instruction_set decoded run with same | inserted
  · rwa [same]
  · rw [inserted]
    intro member
    rcases (Batteries.RBSet.mem_insert (t := before.substate.selfDestructSet)).mp member with earlier | equal
    · exact absent earlier
    · exact accountAddress_compare_ne_eq_of_ne foreign.symm equal

/-- The pinned runtime never selects a self-destruct instruction. -/
theorem runtime_instruction_not_selfdestruct {before : Ethereum.State}
    {op : Operation} {arg : Option (UInt256 × Nat)}
    (code : before.executionEnv.code = runtimeBytecode)
    (decoded : (decode before.executionEnv.code before.machineState.pc).getD (.STOP, none) = (op, arg)) :
    op ≠ .SELFDESTRUCT := by
  have excluded := runtime_no_selfdestruct before.machineState.pc
  rw [← code, decoded] at excluded
  exact excluded

end Rollup.EVM
