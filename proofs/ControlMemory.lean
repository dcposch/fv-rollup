import proofs.support.ControlCursor
import proofs.AbstractPush

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- Machine-state reads push an unrestricted word in the control abstraction. -/
theorem control_machineStateOp {cursor : AbstractCursor} {before after : Ethereum.State}
    (operation : MachineState → UInt256) (represented : cursor.denotes before)
    (run : machineStateOp operation before = .ok after) : (cursor.push .any).denotes after := by
  simp only [machineStateOp, Id.run] at run
  cases Except.ok.inj run
  exact abstract_push 1 represented trivial

/-- Return-data copying removes three words and retains the control cursor. -/
theorem control_returndatacopy_step {cursor next : AbstractCursor} {before after : Ethereum.State}
    {cost : Nat} {arg : Option (UInt256 × Nat)} (represented : cursor.denotes before)
    (advance : cursor.drop 3 = some next)
    (run : step cost (.RETURNDATACOPY, arg) before = .ok after) : next.denotes after := by
  rcases cursor with ⟨pc, abstract⟩
  rcases represented with ⟨counter, relation⟩
  change List.Forall₂ AbstractWord.denotes abstract before.machineState.stack at relation
  generalize stackEq : before.machineState.stack = actual at relation
  cases relation with
  | nil => simp [AbstractCursor.drop] at advance
  | @cons first actualFirst rest actualRest firstKnown tail =>
    cases tail with
    | nil => simp [AbstractCursor.drop] at advance
    | @cons second actualSecond rest actualRest secondKnown tail =>
      cases tail with
      | nil => simp [AbstractCursor.drop] at advance
      | @cons third actualThird rest actualRest thirdKnown tail =>
        simp [AbstractCursor.drop] at advance
        subst next
        simp only [step, stackEq, Stack.pop3] at run
        cases Except.ok.inj run
        constructor
        · exact congrArg (fun value => value + UInt256.ofNat 1) counter
        · exact tail

end Rollup.EVM
