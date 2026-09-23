import semantics.ExecutionPrefix

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- No continuing prefix can pass a failed first instruction. -/
theorem continuing_prefix_entry_error {start current : Ethereum.State} {jumps : Array UInt256}
    {error : ExecutionException} (failed : Xstep jumps start = .error error)
    (trace : ContinuingPrefix jumps start current) : current = start := by
  induction trace with
  | initial => rfl
  | next earlier step ih =>
    rw [ih, failed] at step
    cases step

/-- A frame with a failed first instruction has only its initial visible state. -/
theorem instruction_prefix_entry_error {start current : Ethereum.State} {jumps : Array UInt256}
    {error : ExecutionException} (failed : Xstep jumps start = .error error)
    (trace : InstructionPrefix jumps start current) : current = start := by
  cases trace with
  | current earlier => exact continuing_prefix_entry_error failed earlier
  | afterStep earlier step =>
    rw [continuing_prefix_entry_error failed earlier, failed] at step
    cases step

/-- The creation collision stub fails before it can change the state. -/
theorem invalid_entry_error (state : Ethereum.State) (jumps : Array UInt256)
    (code : state.executionEnv.code = ⟨#[0xfe]⟩) (counter : state.machineState.pc = ⟨0⟩) :
    Xstep jumps state = .error .InvalidInstruction := by
  have decoded : decode state.executionEnv.code state.machineState.pc = some (.INVALID, none) := by
    rw [code, counter]
    decide +kernel
  simp [Xstep, Z, δ, decoded]

end Rollup.EVM
