import proofs.support.AbstractCursor
import Reasoning.Stepping

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- An abstract direct jump includes the exact concrete destination and stack. -/
theorem abstract_jump_step {cursor next : AbstractCursor} {before after : Ethereum.State}
    {cost : Nat} {arg : Option (UInt256 × Nat)} (represented : cursor.denotes before)
    (advance : cursor.jump = some next) (run : step cost (.JUMP, arg) before = .ok after) :
    next.denotes after := by
  rcases cursor with ⟨pc, abstract⟩
  rcases represented with ⟨counter, relation⟩
  change List.Forall₂ AbstractWord.denotes abstract before.machineState.stack at relation
  generalize stackEq : before.machineState.stack = actual at relation
  cases relation with
  | nil => simp [AbstractCursor.jump, Stack.pop] at advance
  | @cons destination actualDestination rest actualRest known tail =>
    cases destination with
    | any => simp [AbstractCursor.jump, Stack.pop] at advance
    | nonzero => simp [AbstractCursor.jump, Stack.pop] at advance
    | exact target =>
      change actualDestination = target at known
      subst actualDestination
      simp only [AbstractCursor.jump, Stack.pop, bind, Option.bind, pure] at advance
      cases Option.some.inj advance
      simp only [step, stackEq, Stack.pop] at run
      cases Except.ok.inj run
      exact ⟨rfl, tail⟩

/-- Abstract conditional jumps include both possible concrete branches. -/
theorem abstract_jumpIf_step {cursor : AbstractCursor} {next : List AbstractCursor}
    {before after : Ethereum.State} {cost : Nat} {arg : Option (UInt256 × Nat)}
    (represented : cursor.denotes before) (advance : cursor.jumpIf = some next)
    (run : step cost (.JUMPI, arg) before = .ok after) :
    ∃ following ∈ next, following.denotes after := by
  rcases cursor with ⟨pc, abstract⟩
  rcases represented with ⟨counter, relation⟩
  change List.Forall₂ AbstractWord.denotes abstract before.machineState.stack at relation
  generalize stackEq : before.machineState.stack = actual at relation
  cases relation with
  | nil => simp [AbstractCursor.jumpIf, Stack.pop2] at advance
  | @cons destination actualDestination rest actualRest known tail =>
    cases tail with
    | nil => simp [AbstractCursor.jumpIf, Stack.pop2] at advance
    | @cons condition actualCondition rest actualRest conditionKnown tail =>
      cases destination with
      | any => simp [AbstractCursor.jumpIf, Stack.pop2] at advance
      | nonzero => simp [AbstractCursor.jumpIf, Stack.pop2] at advance
      | exact target =>
        change actualDestination = target at known
        subst actualDestination
        simp only [step, stackEq, Stack.pop2] at run
        cases Except.ok.inj run
        cases condition with
        | exact value =>
          change actualCondition = value at conditionKnown
          subst actualCondition
          by_cases zero : value = ⟨0⟩
          · simp [AbstractCursor.jumpIf, Stack.pop2, zero] at advance
            subst next
            refine ⟨_, List.mem_singleton_self _, ?_⟩
            exact ⟨by simpa [AbstractCursor.advance, zero] using
              congrArg (fun value => value + UInt256.ofNat 1) counter, tail⟩
          · simp [AbstractCursor.jumpIf, Stack.pop2, zero] at advance
            subst next
            refine ⟨_, List.mem_singleton_self _, ?_⟩
            exact ⟨by simp [zero], tail⟩
        | nonzero =>
          change actualCondition ≠ ⟨0⟩ at conditionKnown
          simp [AbstractCursor.jumpIf, Stack.pop2] at advance
          subst next
          refine ⟨_, List.mem_singleton_self _, ?_⟩
          exact ⟨by simp [conditionKnown], tail⟩
        | any =>
          simp [AbstractCursor.jumpIf, Stack.pop2] at advance
          subst next
          by_cases zero : actualCondition = ⟨0⟩
          · refine ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), ?_⟩
            exact ⟨by simpa [AbstractCursor.advance, zero] using
              congrArg (fun value => value + UInt256.ofNat 1) counter, tail⟩
          · refine ⟨_, List.mem_cons_self, ?_⟩
            exact ⟨by simp [zero], tail⟩

end Rollup.EVM
