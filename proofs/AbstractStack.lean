import proofs.support.AbstractCursor
import Mathlib.Data.List.Forall2

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- A represented stack element has a concrete value at the same index. -/
theorem abstract_stack_get {abstract : List AbstractWord} {actual : List UInt256}
    (represented : AbstractStackDenotes abstract actual) {index : Nat} {value : AbstractWord}
    (found : abstract[index]? = some value) :
    ∃ actualValue, actual[index]? = some actualValue ∧ value.denotes actualValue := by
  obtain ⟨bounded, same⟩ := List.getElem?_eq_some_iff.mp found
  have actualBound : index < actual.length := by rwa [← represented.length_eq]
  refine ⟨actual[index], List.getElem?_eq_some_iff.mpr ⟨actualBound, rfl⟩, ?_⟩
  simpa only [List.get_eq_getElem, same] using represented.get bounded actualBound

/-- Replacing corresponding stack elements preserves representation. -/
theorem abstract_stack_set {abstract : List AbstractWord} {actual : List UInt256}
    (represented : AbstractStackDenotes abstract actual) (index : Nat)
    {value : AbstractWord} {actualValue : UInt256} (known : value.denotes actualValue) :
    AbstractStackDenotes (abstract.set index value) (actual.set index actualValue) := by
  induction represented generalizing index with
  | nil => exact List.Forall₂.nil
  | cons head tail ih =>
    cases index with
    | zero => exact List.Forall₂.cons known tail
    | succ index => exact List.Forall₂.cons head (ih index)

/-- The abstract DUP result includes the concrete EVM helper result. -/
theorem abstract_duplicate {cursor next : AbstractCursor} {before after : Ethereum.State}
    (index : Nat) (represented : cursor.denotes before)
    (advance : cursor.duplicate index = some next)
    (run : dup (index + 1) before = .ok after) : next.denotes after := by
  unfold AbstractCursor.duplicate at advance
  cases found : cursor.stack[index]? with
  | none => simp [found] at advance
  | some value =>
    simp [found] at advance
    subst next
    obtain ⟨actualValue, actualFound, known⟩ := abstract_stack_get represented.2 found
    have bounded := (List.getElem?_eq_some_iff.mp actualFound).1
    have topSize : (before.machineState.stack.take (index + 1)).length = index + 1 := by
      simp only [List.length_take]
      omega
    have last : (before.machineState.stack.take (index + 1)).getLast! = actualValue := by
      apply List.getLast!_of_getLast?
      simp [List.getLast?_take, actualFound]
    simp only [dup, topSize, if_true, last] at run
    cases Except.ok.inj run
    exact ⟨congrArg (fun value => value + UInt256.ofNat 1) represented.1,
      List.Forall₂.cons known represented.2⟩

end Rollup.EVM
