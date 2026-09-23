import proofs.support.AbstractCursor

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- Pushing a represented value preserves the stack relation and advances the counter. -/
theorem abstract_push {cursor : AbstractCursor} {before : Ethereum.State}
    {value : AbstractWord} {actual : UInt256} (width : Nat)
    (represented : cursor.denotes before) (known : value.denotes actual) :
    (cursor.push value width).denotes
      (before.replaceStackAndIncrPC (before.machineState.stack.push actual) width) := by
  exact ⟨congrArg (fun pc => pc + UInt256.ofNat width) represented.1,
    List.Forall₂.cons known represented.2⟩

/-- Environment reads have unrestricted abstract values. -/
theorem abstract_executionEnvOp {cursor : AbstractCursor} {before after : Ethereum.State}
    (operation : ExecutionEnv → UInt256) (represented : cursor.denotes before)
    (run : executionEnvOp operation before = .ok after) : (cursor.push .any).denotes after := by
  simp only [executionEnvOp, Id.run] at run
  cases Except.ok.inj run
  exact abstract_push 1 represented trivial

/-- PUSH0 pushes an exact zero in both executions. -/
theorem abstract_push0_step {cursor : AbstractCursor} {before after : Ethereum.State}
    {cost : Nat} {arg : Option (UInt256 × Nat)} (represented : cursor.denotes before)
    (run : step cost (.PUSH0, arg) before = .ok after) :
    (cursor.push (.exact ⟨0⟩)).denotes after := by
  simp only [step] at run
  cases Except.ok.inj run
  exact abstract_push 1 represented rfl

/-- Every immediate PUSH uses the same word and instruction width in both executions. -/
theorem abstract_push_step {cursor : AbstractCursor} {before after : Ethereum.State}
    {cost width : Nat} {value : UInt256} {kind : Operation.POp}
    (nonzero : kind ≠ .PUSH0) (represented : cursor.denotes before)
    (run : step cost (.Push kind, some (value, width)) before = .ok after) :
    (cursor.push (.exact value) (width + 1)).denotes after := by
  cases kind
  all_goals first
    | exact (nonzero rfl).elim
    | (simp only [step] at run
       cases Except.ok.inj run
       exact abstract_push (width + 1) represented rfl)

/-- JUMPDEST changes only the program counter in the abstract cursor. -/
theorem abstract_jumpdest_step {cursor : AbstractCursor} {before after : Ethereum.State}
    {cost : Nat} {arg : Option (UInt256 × Nat)} (represented : cursor.denotes before)
    (run : step cost (.JUMPDEST, arg) before = .ok after) :
    (cursor.advance cursor.stack).denotes after := by
  simp only [step] at run
  cases Except.ok.inj run
  exact ⟨congrArg (fun value => value + UInt256.ofNat 1) represented.1, represented.2⟩

end Rollup.EVM
