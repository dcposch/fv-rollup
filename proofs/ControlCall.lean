import proofs.support.ControlCursor
import Ethereum.Theory.GasLemmas
import Mathlib.Data.List.Forall2

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- The call helper preserves the parent's program counter. -/
theorem call_helper_counter {before after : Ethereum.State} {returned : UInt256}
    {cost : Nat} {blobs : List ByteArray} {gas source recipient target value contextValue : UInt256}
    {inOffset inSize outOffset outSize : UInt256} {permission : Bool}
    (run : call cost blobs gas source recipient target value contextValue inOffset inSize outOffset outSize
      permission before = .ok (returned, after)) : after.machineState.pc = before.machineState.pc := by
  unfold call at run
  exact (congrArg (fun pair => pair.2.machineState.pc) (Except.ok.inj run)).symm

private theorem pop7_rest {stack rest : Stack UInt256} {a b c d e f g : UInt256}
    (popped : stack.pop7 = some (rest, a, b, c, d, e, f, g)) : rest = stack.drop 7 := by
  unfold Stack.pop7 at popped
  split at popped <;> try contradiction
  cases Option.some.inj popped
  rfl

/-- CALL advances one byte and replaces seven inputs with its status word. -/
theorem call_step_cursor {before after : Ethereum.State} {cost : Nat} {arg : Option (UInt256 × Nat)}
    (run : step cost (.CALL, arg) before = .ok after) :
    after.machineState.pc = before.machineState.pc + UInt256.ofNat 1 ∧
      ∃ returned, after.machineState.stack = returned :: before.machineState.stack.drop 7 := by
  simp only [step, bind, Except.bind] at run
  split at run <;> try contradiction
  rename_i popped pop
  split at run <;> try contradiction
  rename_i outcome executed
  rcases popped with ⟨rest, gas, target, value, inOffset, inSize, outOffset, outSize⟩
  rcases outcome with ⟨returned, during⟩
  have counter := call_helper_counter executed
  have tail := pop7_rest (option_liftM_eq_some pop)
  have same := Except.ok.inj run
  rw [← same]
  exact ⟨congrArg (fun pc => pc + UInt256.ofNat 1) counter,
    returned, congrArg (List.cons returned) tail⟩

/-- The abstract CALL result includes every concrete status word. -/
theorem control_call_step {cursor next : AbstractCursor} {before after : Ethereum.State}
    {cost : Nat} {arg : Option (UInt256 × Nat)} (represented : cursor.denotes before)
    (advance : cursor.replacePrefix 7 1 = some next)
    (run : step cost (.CALL, arg) before = .ok after) : next.denotes after := by
  unfold AbstractCursor.replacePrefix at advance
  split at advance <;> try contradiction
  cases Option.some.inj advance
  obtain ⟨counter, returned, stack⟩ := call_step_cursor run
  constructor
  · exact counter.trans (congrArg (fun pc => pc + UInt256.ofNat 1) represented.1)
  · change List.Forall₂ AbstractWord.denotes (.any :: cursor.stack.drop 7) after.machineState.stack
    rw [stack]
    exact List.Forall₂.cons trivial (List.forall₂_drop 7 represented.2)

end Rollup.EVM
