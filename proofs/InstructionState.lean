import proofs.InstructionStep

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- A successful instruction exposes the exact state returned by its opcode. -/
theorem instruction_state_step {before after : Ethereum.State} {jumps : Array UInt256}
    {op : Operation} {arg : Option (UInt256 × Nat)} {ret}
    (decoded : (decode before.executionEnv.code before.machineState.pc).getD (.STOP, none) = (op, arg))
    (run : Xstep jumps before = .ok (after, ret)) :
    ∃ checked cost stepped,
      Z jumps op before = .ok (checked, cost) ∧
      step cost (op, arg) { checked with executionEnv.depth := before.executionEnv.depth } = .ok stepped ∧
      after = { stepped with executionEnv := before.executionEnv } := by
  simp [Xstep, decoded] at run
  split at run
  · contradiction
  · rename_i checked cost check
    simp [bind, Except.bind] at run
    split at run
    · contradiction
    · rename_i stepped execute
      have precheck : Z jumps op before = .ok (checked, cost) := by
        simpa [decoded] using check
      have opcode : step cost (op, arg)
          { checked with executionEnv.depth := before.executionEnv.depth } = .ok stepped := by
        simpa [decoded] using execute
      repeat' first | split at run | contradiction
      all_goals exact ⟨checked, cost, stepped, precheck, opcode,
        (congrArg Prod.fst (Except.ok.inj run)).symm⟩

end Rollup.EVM
