import proofs.support.AbstractCursor

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- POP removes one represented word. -/
theorem abstract_pop_step {cursor next : AbstractCursor} {before after : Ethereum.State}
    {cost : Nat} {arg : Option (UInt256 × Nat)} (represented : cursor.denotes before)
    (advance : cursor.drop 1 = some next) (run : step cost (.POP, arg) before = .ok after) :
    next.denotes after := by
  rcases cursor with ⟨pc, abstract⟩
  rcases represented with ⟨counter, relation⟩
  change List.Forall₂ AbstractWord.denotes abstract before.machineState.stack at relation
  generalize stackEq : before.machineState.stack = actual at relation
  cases relation with
  | nil => simp [AbstractCursor.drop] at advance
  | @cons value actualValue rest actualRest known tail =>
    simp [AbstractCursor.drop] at advance
    subst next
    simp only [step, stackEq, Stack.pop] at run
    cases Except.ok.inj run
    exact ⟨congrArg (fun value => value + UInt256.ofNat 1) counter, tail⟩

/-- MSTORE removes two words and leaves the remaining stack unchanged. -/
theorem abstract_mstore_step {cursor next : AbstractCursor} {before after : Ethereum.State}
    {cost : Nat} {arg : Option (UInt256 × Nat)} (represented : cursor.denotes before)
    (advance : cursor.drop 2 = some next) (run : step cost (.MSTORE, arg) before = .ok after) :
    next.denotes after := by
  rcases cursor with ⟨pc, abstract⟩
  rcases represented with ⟨counter, relation⟩
  change List.Forall₂ AbstractWord.denotes abstract before.machineState.stack at relation
  generalize stackEq : before.machineState.stack = actual at relation
  cases relation with
  | nil => simp [AbstractCursor.drop] at advance
  | @cons left actualLeft rest actualRest leftKnown tail =>
    cases tail with
    | nil => simp [AbstractCursor.drop] at advance
    | @cons right actualRight rest actualRest rightKnown tail =>
      simp [AbstractCursor.drop] at advance
      subst next
      simp only [step, binaryMachineStateOp, stackEq, Stack.pop2, Id.run] at run
      cases Except.ok.inj run
      constructor
      · simpa only [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC,
          MachineState.mstore, MachineState.writeWord, AbstractCursor.advance]
          using congrArg (fun value => value + UInt256.ofNat 1) counter
      · exact tail

end Rollup.EVM
