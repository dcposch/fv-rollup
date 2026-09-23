import proofs.AbstractStack

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- The EVM swap helper replaces the top and indexed elements of a valid stack. -/
theorem swap_stack_shape (stack : List UInt256) (index : Nat)
    (positive : 0 < index) (bounded : index < stack.length) :
    (stack.take (index + 1)).getLast! ::
      (stack.take (index + 1)).tail!.dropLast ++
      [(stack.take (index + 1)).head!] ++ stack.drop (index + 1) =
    (stack.set 0 stack[index]).set index stack[0] := by
  cases index with
  | zero => omega
  | succ index =>
    cases stack with
    | nil => simp at bounded
    | cons first rest =>
      have restBound : index < rest.length := by simpa using bounded
      have last : ((first :: rest).take (index + 2)).getLast! = rest[index] := by
        apply List.getLast!_of_getLast?
        rw [List.getLast?_take]
        simp [restBound]
      have middle : (rest.take (index + 1)).dropLast = rest.take index := by
        rw [List.dropLast_eq_take, List.length_take, Nat.min_eq_left (by omega), List.take_take]
        simp
      rw [last]
      simp only [List.take_succ_cons, List.tail!_cons,
        List.head!_cons, List.drop_succ_cons, List.getElem_cons_succ, List.getElem_cons_zero,
        List.set_cons_zero, List.set_cons_succ, middle]
      rw [List.set_eq_take_append_cons_drop, if_pos restBound]
      simp

/-- The abstract SWAP result includes the concrete EVM helper result. -/
theorem abstract_exchange {cursor next : AbstractCursor} {before after : Ethereum.State}
    (index : Nat) (positive : 0 < index) (represented : cursor.denotes before)
    (advance : cursor.exchange index = some next) (run : swap index before = .ok after) :
    next.denotes after := by
  unfold AbstractCursor.exchange at advance
  cases firstFound : cursor.stack[0]? with
  | none => simp [firstFound] at advance
  | some first =>
    cases otherFound : cursor.stack[index]? with
    | none => simp [firstFound, otherFound] at advance
    | some other =>
      simp [firstFound, otherFound] at advance
      subst next
      obtain ⟨actualFirst, firstAt, firstKnown⟩ := abstract_stack_get represented.2 firstFound
      obtain ⟨actualOther, otherAt, otherKnown⟩ := abstract_stack_get represented.2 otherFound
      obtain ⟨firstBound, firstSame⟩ := List.getElem?_eq_some_iff.mp firstAt
      obtain ⟨otherBound, otherSame⟩ := List.getElem?_eq_some_iff.mp otherAt
      have topSize : (before.machineState.stack.take (index + 1)).length = index + 1 := by
        simp only [List.length_take]
        omega
      simp only [swap, topSize, if_true] at run
      rw [swap_stack_shape _ index positive otherBound, firstSame, otherSame] at run
      cases Except.ok.inj run
      exact ⟨congrArg (fun value => value + UInt256.ofNat 1) represented.1,
        abstract_stack_set (abstract_stack_set represented.2 0 otherKnown) index firstKnown⟩

end Rollup.EVM
