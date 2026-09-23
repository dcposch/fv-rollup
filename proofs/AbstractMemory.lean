import proofs.support.AbstractCursor

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- A read with no state change can return any word in the abstract stack. -/
theorem abstract_unary_read {cursor next : AbstractCursor} {before after : Ethereum.State}
    (operation : Ethereum.State → UInt256 → UInt256) (represented : cursor.denotes before)
    (advance : cursor.unary (fun _ => .any) = some next)
    (run : unaryStateOp (fun state value => (state, operation state value)) before = .ok after) :
    next.denotes after := by
  rcases cursor with ⟨pc, abstract⟩
  rcases represented with ⟨counter, relation⟩
  change List.Forall₂ AbstractWord.denotes abstract before.machineState.stack at relation
  generalize stackEq : before.machineState.stack = actual at relation
  cases relation with
  | nil => simp [AbstractCursor.unary, Stack.pop] at advance
  | @cons value actualValue rest actualRest known tail =>
    simp only [AbstractCursor.unary, Stack.pop, bind, Option.bind, pure] at advance
    cases Option.some.inj advance
    simp only [unaryStateOp, stackEq, Stack.pop, Id.run] at run
    cases Except.ok.inj run
    exact ⟨congrArg (fun value => value + UInt256.ofNat 1) counter, List.Forall₂.cons trivial tail⟩

/-- The abstract memory load includes every concrete memory word. -/
theorem abstract_mload_step {cursor next : AbstractCursor} {before after : Ethereum.State}
    {cost : Nat} {arg : Option (UInt256 × Nat)} (represented : cursor.denotes before)
    (advance : cursor.unary (fun _ => .any) = some next)
    (run : step cost (.MLOAD, arg) before = .ok after) : next.denotes after := by
  rcases cursor with ⟨pc, abstract⟩
  rcases represented with ⟨counter, relation⟩
  change List.Forall₂ AbstractWord.denotes abstract before.machineState.stack at relation
  generalize stackEq : before.machineState.stack = actual at relation
  cases relation with
  | nil => simp [AbstractCursor.unary, Stack.pop] at advance
  | @cons value actualValue rest actualRest known tail =>
    simp only [AbstractCursor.unary, Stack.pop, bind, Option.bind, pure] at advance
    cases Option.some.inj advance
    simp only [step, stackEq, Stack.pop, Id.run] at run
    cases Except.ok.inj run
    constructor
    · simpa only [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC,
        MachineState.mload, AbstractCursor.advance]
        using congrArg (fun value => value + UInt256.ofNat 1) counter
    · exact List.Forall₂.cons trivial tail

/-- The abstract hash result includes every concrete Keccak output. -/
theorem abstract_keccak_step {cursor next : AbstractCursor} {before after : Ethereum.State}
    {cost : Nat} {arg : Option (UInt256 × Nat)} (represented : cursor.denotes before)
    (advance : cursor.binary (fun _ _ => .any) = some next)
    (run : step cost (.KECCAK256, arg) before = .ok after) : next.denotes after := by
  rcases cursor with ⟨pc, abstract⟩
  rcases represented with ⟨counter, relation⟩
  change List.Forall₂ AbstractWord.denotes abstract before.machineState.stack at relation
  generalize stackEq : before.machineState.stack = actual at relation
  cases relation with
  | nil => simp [AbstractCursor.binary, Stack.pop2] at advance
  | @cons left actualLeft rest actualRest leftKnown tail =>
    cases tail with
    | nil => simp [AbstractCursor.binary, Stack.pop2] at advance
    | @cons right actualRight rest actualRest rightKnown tail =>
      simp only [AbstractCursor.binary, Stack.pop2, bind, Option.bind, pure] at advance
      cases Option.some.inj advance
      simp only [step, binaryMachineStateOp', stackEq, Stack.pop2, Id.run] at run
      cases Except.ok.inj run
      constructor
      · simpa only [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC,
          MachineState.keccak256, AbstractCursor.advance]
          using congrArg (fun value => value + UInt256.ofNat 1) counter
      · exact List.Forall₂.cons trivial tail

end Rollup.EVM
