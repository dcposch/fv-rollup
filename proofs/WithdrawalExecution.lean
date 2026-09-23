import proofs.WithdrawalSource

open Solm ABI Ethereum Reasoning.Theory

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Rollup.EVM

private theorem payment_environment {before after : Ethereum.State} {owner : Address}
    {amount : Int} {input data : ByteArray} {paid perm : Bool}
    (call : callViaEVM before owner amount input (paid, after, data) perm) :
    after.executionEnv = before.executionEnv := by
  cases call <;> subst_vars <;> rfl

private theorem withdrawal_call_step (evm after : Ethereum.State) (owner : Address) (amount : Nat)
    (paid : Bool) (data : ByteArray)
    (call : callViaEVM (withdrawalLockedState evm) owner amount ByteArray.empty (paid, after, data)) :
    ExecStmt config ⟨contract, withdrawalCreditLocals evm owner amount⟩ (withdrawalLockedState evm)
      (.lowLevelCall (.var "owner") (.var "amount") (.newBytes (.intLit 0)) "success" "_data")
      (.ok ⟨contract, withdrawalReturnLocals evm owner amount paid data⟩ after) := by
  have ownerArg : (withdrawalCreditLocals evm owner amount).get? "owner" = some (.address owner) := by
    dsimp only [withdrawalCreditLocals, withdrawalLocals]
    repeat rw [store_get_ne _ _ (by decide)]
    exact store_get_self _ _ _
  have amountArg : (withdrawalCreditLocals evm owner amount).get? "amount" = some (.int amount) := by
    dsimp only [withdrawalCreditLocals, withdrawalLocals]
    repeat rw [store_get_ne _ _ (by decide)]
    exact store_get_self _ _ _
  have receiver : evalExpr? config ⟨contract, withdrawalCreditLocals evm owner amount⟩ (withdrawalLockedState evm)
      (.var "owner") = .ok (.address owner) := by
    simp only [evalExpr?, ownerArg, EvalResult.ofOption]
  have value : evalExpr? config ⟨contract, withdrawalCreditLocals evm owner amount⟩ (withdrawalLockedState evm)
      (.var "amount") = .ok (.int amount) := by
    simp only [evalExpr?, amountArg, EvalResult.ofOption]
  have input : evalExpr? config ⟨contract, withdrawalCreditLocals evm owner amount⟩ (withdrawalLockedState evm)
      (.newBytes (.intLit 0)) = .ok (.bytes ByteArray.empty) := by
    simp only [evalExpr?, bind, EvalResult.bind, pure]
    rfl
  have target : _root_.EVM.address owner.val = owner := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt owner.isLt
  cases paid
  · exact .lowLevelCallFailure receiver value input (by simpa only [target] using call)
  · exact .lowLevelCallSuccess receiver value input (by simpa only [target] using call)

/-- Failed entry checks give a full source revert before payment. -/
theorem withdrawal_body_rejected_checks (evm : Ethereum.State) (owner : Address) (amount : Nat)
    (failed : ¬ WithdrawalExecutionChecks evm owner amount) :
    ExecTransitionBody config contract evm (withdrawalLocals owner amount)
      contract.transitions[2]!.body .reverted := by
  have block := execBlock_append_term (s2 := contract.transitions[2]!.body.drop 6)
    (withdrawal_prelude_rejected evm owner amount failed).run (by intros; intro same; cases same)
  exact .execBlockRevert block

/-- An actual EVM payment determines source completion or source revert. -/
theorem withdrawal_body_payment (evm after : Ethereum.State) (owner : Address) (amount : Nat)
    (paid : Bool) (data : ByteArray)
    (checks : WithdrawalExecutionChecks evm owner amount)
    (call : callViaEVM (withdrawalLockedState evm) owner amount ByteArray.empty (paid, after, data)) :
    ExecTransitionBody config contract evm (withdrawalLocals owner amount) contract.transitions[2]!.body
      (if paid then .returned ⟨contract, withdrawalReturnLocals evm owner amount true data⟩
        (withdrawalFinalState evm after owner amount) none else .reverted) := by
  have preludeRun := (withdrawal_prelude_exact evm owner amount checks).run
  have payment := withdrawal_call_step evm after owner amount paid data call
  cases paid
  · have tail := (withdrawal_postlude_rejected evm after owner amount data).run
    exact .execBlockRevert (execBlock_append preludeRun (.consNormal payment tail))
  · have tail := (withdrawal_postlude_exact evm after owner amount data checks.covered).run
    exact .execBlockOK (execBlock_append preludeRun (.consNormal payment tail))

/-- Every accepted source withdrawal makes the specified payment before the exact debit and unlock. -/
theorem withdrawal_source_exact (evm out : Ethereum.State) (owner : Address) (amount : Nat)
    (frame : Frame) (values : Option (List Value))
    (run : ExecTransitionBody config contract evm (withdrawalLocals owner amount)
      contract.transitions[2]!.body (.returned frame out values)) :
    values = none ∧ WithdrawalExecutionChecks evm owner amount ∧
      ∃ after data,
        callViaEVM (withdrawalLockedState evm) owner amount ByteArray.empty (true, after, data) ∧
        after.executionEnv = evm.executionEnv ∧
        frame = ⟨contract, withdrawalReturnLocals evm owner amount true data⟩ ∧
        out = withdrawalFinalState evm after owner amount := by
  have ownerArg : (withdrawalLocals owner amount).get? "owner" = some (.address owner) := by
    rw [withdrawalLocals, store_get_ne _ _ (by decide), store_get_self]
  have amountArg : (withdrawalLocals owner amount).get? "amount" = some (.int amount) := store_get_self _ _ _
  obtain ⟨empty, middle, before, after, data, preludeRun, _, _, call, tail⟩ :=
    withdrawal_payment_witness evm out (withdrawalLocals owner amount) frame owner amount values
      ownerArg amountArg run
  obtain ⟨checks, middleEq, beforeEq⟩ := withdrawal_prelude_result evm before owner amount middle preludeRun
  subst middle
  subst before
  have same := (withdrawal_postlude_exact evm after owner amount data checks.covered).unique _ tail
  have env : after.executionEnv = evm.executionEnv := by
    simpa only [withdrawalLockedState, storageStore_executionEnv] using payment_environment call
  exact ⟨empty, checks, after, data, call, env, ExecResult.ok.inj same⟩

end Rollup.EVM
