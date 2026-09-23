import semantics.Payments
import proofs.SourceSteps
import proofs.SolmGuards

open Solm Reasoning.Theory

namespace Rollup.EVM

/-- An accepted source withdrawal contains an actual successful EVM payment call. -/
theorem withdrawal_payment_witness (evm out : Ethereum.State) (locals : Store) (frame : Frame)
    (owner : Address) (amount : Nat) (values : Option (List Value))
    (ownerArg : locals.get? "owner" = some (.address owner))
    (amountArg : locals.get? "amount" = some (.int amount))
    (run : ExecTransitionBody config contract evm locals contract.transitions[2]!.body
      (.returned frame out values)) :
    values = none ∧ WithdrawalPayment evm out locals frame owner amount := by
  obtain ⟨noReturn, block⟩ := plain_function_success (by decide) run
  refine ⟨noReturn, ?_⟩
  change ExecBlock config ⟨contract, locals⟩ evm
    (withdrawalPrelude ++ .lowLevelCall (.var "owner") (.var "amount")
      (.newBytes (.intLit 0)) "success" "_data" :: withdrawalPostlude) (.ok frame out) at block
  obtain ⟨middle, before, left, right⟩ := split_block_success block
  have ownerPreserved := block_preserves_local "owner" (by decide) left
  have amountPreserved := block_preserves_local "amount" (by decide) left
  have receiver : evalExpr? config middle before (.var "owner") = .ok (.address owner) := by
    simp only [evalExpr?, ownerPreserved, ownerArg, EvalResult.ofOption]
  have amountEval : evalExpr? config middle before (.var "amount") = .ok (.int amount) := by
    simp only [evalExpr?, amountPreserved, amountArg, EvalResult.ofOption]
  have emptyData : evalExpr? config middle before (.newBytes (.intLit 0)) =
      .ok (.bytes ByteArray.empty) := by
    simp only [evalExpr?, bind, EvalResult.bind, pure]
    rfl
  cases right with
  | consNormal callStep tail =>
    cases callStep with
    | lowLevelCallSuccess targetEval sentEval dataEval call =>
      rw [receiver] at targetEval
      rw [amountEval] at sentEval
      rw [emptyData] at dataEval
      cases targetEval
      cases sentEval
      cases dataEval
      have target : _root_.EVM.address owner.val = owner := by
        apply Fin.ext
        exact Nat.mod_eq_of_lt owner.isLt
      rw [target] at call
      exact ⟨middle, before, _, _, left, receiver, amountEval, call, tail⟩
    | lowLevelCallFailure targetEval sentEval dataEval call =>
      have falseGuard (data : ByteArray) (after : Ethereum.State) : evalExpr? config
          { middle with locals := (middle.locals.insert "success" (.bool false)).insert "_data" (.bytes data) }
          after (.var "success") = .ok (.bool false) := by
        simp only [evalExpr?]
        rw [store_get_ne _ _ (by decide), store_get_self]
        rfl
      have impossible := require_false_only_reverts (falseGuard _ _) tail
      cases impossible

theorem source_payment_bound (evm out : Ethereum.State) (locals : Store) (frame : Frame)
    (call : Call) (values : Option (List Value))
    (bound : CallBound evm locals call)
    (run : ExecTransitionBody config contract evm locals (entryTransition call.entry).body
      (.returned frame out values)) : PaymentBound evm out locals frame call.entry := by
  obtain ⟨caller, value, entry⟩ := call
  cases entry with
  | deposit => trivial
  | executeBatch => trivial
  | read => trivial
  | withdrawPendingBalance owner amount =>
    have args := bound.2.2.2.2
    change some (((∅ : Store).insert "owner" (.address owner)).insert "amount" (.int amount)) =
      some locals at args
    have localEq := Option.some.inj args
    subst locals
    apply (withdrawal_payment_witness evm out _ frame owner amount values ?_ ?_ run).2
    · rw [store_get_ne _ _ (by decide), store_get_self]
    · exact store_get_self _ _ _

end Rollup.EVM
