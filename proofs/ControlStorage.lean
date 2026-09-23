import proofs.support.ControlCursor
import proofs.AbstractExecution
import proofs.AbstractMemory
import Mathlib.Data.List.Forall2

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- A storage load has an unrestricted result in the control-flow abstraction. -/
theorem control_execSload {cursor next : AbstractCursor} {before after : Ethereum.State}
    (represented : cursor.denotes before)
    (advance : cursor.unary (fun _ => .any) = some next)
    (run : unaryStateOp Ethereum.State.sload before = .ok after) : next.denotes after := by
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
    constructor
    · simpa only [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC,
        Ethereum.State.sload, Ethereum.State.addAccessedStorageKey, AbstractCursor.advance]
        using congrArg (fun value => value + UInt256.ofNat 1) counter
    · exact List.Forall₂.cons trivial tail

private theorem sstore_pc (state : Ethereum.State) (slot value : UInt256) :
    (state.sstore slot value).machineState.pc = state.machineState.pc := by
  unfold Ethereum.State.sstore
  cases found : state.lookupAccount state.executionEnv.codeOwner <;>
    simp [Option.option, found, Ethereum.State.setAccount, Ethereum.State.addAccessedStorageKey]

/-- SSTORE removes two words and leaves the remaining stack unchanged. -/
theorem control_sstore_step {cursor next : AbstractCursor} {before after : Ethereum.State}
    {cost : Nat} {arg : Option (UInt256 × Nat)} (represented : cursor.denotes before)
    (advance : cursor.drop 2 = some next) (run : step cost (.SSTORE, arg) before = .ok after) :
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
      simp only [step, binaryStateOp, stackEq, Stack.pop2, Id.run] at run
      cases Except.ok.inj run
      constructor
      · simpa only [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC,
          sstore_pc, AbstractCursor.advance]
          using congrArg (fun value => value + UInt256.ofNat 1) counter
      · exact tail

end Rollup.EVM
