import proofs.InstructionState

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- A continuing instruction is not a halting or invalid opcode. -/
theorem continuing_instruction_kind {before after : Ethereum.State} {jumps : Array UInt256}
    {op : Operation} {arg : Option (UInt256 × Nat)}
    (decoded : (decode before.executionEnv.code before.machineState.pc).getD (.STOP, none) = (op, arg))
    (run : Xstep jumps before = .ok (after, none)) :
    op ≠ .STOP ∧ op ≠ .RETURN ∧ op ≠ .REVERT ∧ op ≠ .INVALID := by
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals intro same; subst op
  case refine_4 => simp [Xstep, decoded, Z, δ] at run
  all_goals
    simp [Xstep, decoded] at run
    split at run
    · contradiction
    · simp [bind, Except.bind] at run
      split at run <;> simp_all

end Rollup.EVM
