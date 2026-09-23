import proofs.support.AccountSurvival
import proofs.LocalCode
import proofs.CreationSetLocal
import proofs.DestructionInstruction
import proofs.DestructionFrame

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- Instruction validation preserves code and both account lifecycle sets. -/
theorem precheck_survives {self : Address} {before after : Ethereum.State}
    {jumps : Array UInt256} {op : Operation} {cost : Nat}
    (initial : StateSurvives self before) (run : Z jumps op before = .ok (after, cost)) :
    StateSurvives self after := by
  refine ⟨?_, ?_, ?_⟩
  · rw [precheck_accounts run]
    exact (AccountSurvives.pinned initial)
  · rw [precheck_created_set run]
    exact (AccountSurvives.notCreated initial)
  · rw [precheck_destruct_set run]
    exact (AccountSurvives.notDeleted initial)

/-- Local instructions preserve an existing rollup in every storage context. -/
theorem local_step_survives {self : Address} {before after : Ethereum.State} {cost : Nat}
    {op : Operation} {arg : Option (UInt256 × Nat)}
    (initial : StateSurvives self before) (internal : LocalOperation op)
    (run : step cost (op, arg) before = .ok after) : StateSurvives self after := by
  refine ⟨(local_step_code internal run self).symm.trans (AccountSurvives.pinned initial), ?_, ?_⟩
  · rw [local_step_created_set internal run]
    exact (AccountSurvives.notCreated initial)
  · rw [local_step_destruct_set internal run]
    exact (AccountSurvives.notDeleted initial)

/-- Self-destruct can schedule its owner only when that owner was created in this transaction. -/
theorem selfdestruct_created_guard {before after : Ethereum.State} {cost : Nat}
    {arg : Option (UInt256 × Nat)} (run : step cost (.SELFDESTRUCT, arg) before = .ok after) :
    after.createdAccounts = before.createdAccounts ∧
      (after.substate.selfDestructSet = before.substate.selfDestructSet ∨
        (before.executionEnv.codeOwner ∈ before.createdAccounts ∧
          after.substate.selfDestructSet = before.substate.selfDestructSet.insert before.executionEnv.codeOwner)) := by
  simp only [step] at run
  split at run <;> try contradiction
  split at run
  · rename_i created
    have same := Except.ok.inj run
    rw [← same]
    refine ⟨rfl, .inr ⟨?_, rfl⟩⟩
    exact (Batteries.RBSet.contains_iff (t := before.createdAccounts)).mp created
  · have same := Except.ok.inj run
    rw [← same]
    exact ⟨rfl, .inl rfl⟩

/-- An existing rollup cannot enter the deletion set, even if it executes self-destruct. -/
theorem selfdestruct_step_survives {self : Address} {before after : Ethereum.State} {cost : Nat}
    {arg : Option (UInt256 × Nat)} (initial : StateSurvives self before)
    (run : step cost (.SELFDESTRUCT, arg) before = .ok after) : StateSurvives self after := by
  have metadata := selfdestruct_created_guard run
  have code := (selfdestruct_step_static run self).2.2
  refine ⟨code.symm.trans (AccountSurvives.pinned initial), ?_, ?_⟩
  · rw [metadata.1]
    exact (AccountSurvives.notCreated initial)
  · rcases metadata.2 with same | ⟨created, inserted⟩
    · rw [same]
      exact AccountSurvives.notDeleted initial
    · rw [inserted]
      have different : self ≠ before.executionEnv.codeOwner := by
        intro same
        exact (AccountSurvives.notCreated initial) (same.symm ▸ created)
      intro member
      rcases (Batteries.RBSet.mem_insert (t := before.substate.selfDestructSet)).mp member with old | same
      · exact (AccountSurvives.notDeleted initial) old
      · exact accountAddress_compare_ne_eq_of_ne different.symm same

/-- Validation and a local opcode preserve the account lifecycle conditions. -/
theorem local_instruction_survives {self : Address} {before after : Ethereum.State}
    {jumps : Array UInt256} {op : Operation} {arg : Option (UInt256 × Nat)} {ret}
    (initial : StateSurvives self before) (internal : LocalOperation op)
    (decoded : (decode before.executionEnv.code before.machineState.pc).getD (.STOP, none) = (op, arg))
    (run : Xstep jumps before = .ok (after, ret)) : StateSurvives self after := by
  obtain ⟨checked, cost, stepped, precheck, opcode, same⟩ := instruction_state_step decoded run
  have checkedSurvives := precheck_survives initial precheck
  have result := local_step_survives
    (before := { checked with executionEnv.depth := before.executionEnv.depth }) checkedSurvives internal opcode
  rw [same]
  exact result

/-- The actual self-destruct instruction preserves an existing account's survival conditions. -/
theorem selfdestruct_instruction_survives {self : Address} {before after : Ethereum.State}
    {jumps : Array UInt256} {arg : Option (UInt256 × Nat)} {ret}
    (initial : StateSurvives self before)
    (decoded : (decode before.executionEnv.code before.machineState.pc).getD (.STOP, none) = (.SELFDESTRUCT, arg))
    (run : Xstep jumps before = .ok (after, ret)) : StateSurvives self after := by
  obtain ⟨checked, cost, stepped, precheck, opcode, same⟩ := instruction_state_step decoded run
  have checkedSurvives := precheck_survives initial precheck
  have result := selfdestruct_step_survives
    (before := { checked with executionEnv.depth := before.executionEnv.depth }) checkedSurvives opcode
  rw [same]
  exact result

end Rollup.EVM
