import semantics.ChildCall
import proofs.RollupCallOpcode

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- A continuing prefix is empty or has a first continuing instruction. -/
theorem continuing_prefix_head {jumps : Array UInt256} {start current : Ethereum.State}
    (trace : ContinuingPrefix jumps start current) :
    start = current ∨ ∃ after, Xstep jumps start = .ok (after, none) ∧
      ContinuingPrefix jumps { after with executionEnv.depth := start.executionEnv.depth } current := by
  induction trace with
  | initial => exact .inl rfl
  | @next before after earlier run ih =>
    rcases ih with same | ⟨first, step, rest⟩
    · subst before
      exact .inr ⟨after, run, .initial⟩
    · exact .inr ⟨first, step, .next rest run⟩

/-- A prefix leading to a child must advance past a state that cannot enter that child. -/
theorem child_prefix_head {jumps : Array UInt256} {start current child : Ethereum.State}
    (trace : ContinuingPrefix jumps start current) (entered : ChildCallEntry jumps current child)
    (absent : ¬ ChildCallEntry jumps start child) :
    ∃ after, Xstep jumps start = .ok (after, none) ∧
      ContinuingPrefix jumps { after with executionEnv.depth := start.executionEnv.depth } current := by
  rcases continuing_prefix_head trace with same | next
  · exact (absent (same.symm ▸ entered)).elim
  · exact next

/-- Only the four call opcodes can enter a code child at the current instruction. -/
theorem child_call_opcode {jumps : Array UInt256} {before child : Ethereum.State}
    (entered : ChildCallEntry jumps before child) :
    let op := ((decode before.executionEnv.code before.machineState.pc).getD (.STOP, none)).1
    op = .CALL ∨ op = .CALLCODE ∨ op = .DELEGATECALL ∨ op = .STATICCALL := by
  cases entered with
  | entered instruction precheck arguments enabled selected =>
    rw [instruction]
    exact call_opcode_kind arguments

/-- A non-call instruction must complete before a later code child can start. -/
theorem noncall_prefix_head {jumps : Array UInt256} {start current child : Ethereum.State}
    {op : Operation} {arg : Option (UInt256 × Nat)}
    (decoded : (decode start.executionEnv.code start.machineState.pc).getD (.STOP, none) = (op, arg))
    (noncall : op ≠ .CALL ∧ op ≠ .CALLCODE ∧ op ≠ .DELEGATECALL ∧ op ≠ .STATICCALL)
    (trace : ContinuingPrefix jumps start current) (entered : ChildCallEntry jumps current child) :
    ∃ after, Xstep jumps start = .ok (after, none) ∧
      ContinuingPrefix jumps { after with executionEnv.depth := start.executionEnv.depth } current := by
  apply child_prefix_head trace entered
  intro immediate
  have kind := child_call_opcode immediate
  rw [decoded] at kind
  rcases kind with same | same | same | same
  · exact noncall.1 same
  · exact noncall.2.1 same
  · exact noncall.2.2.1 same
  · exact noncall.2.2.2 same

end Rollup.EVM
