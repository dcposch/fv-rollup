import proofs.DepositChecks

open Solm ABI Ethereum Reasoning.Theory

namespace Rollup.EVM

/-- Source guards with the credit read after the lock write. -/
def DepositExecutionChecks (evm : Ethereum.State) (owner : Address) : Prop :=
  readWord evm evm.executionEnv.codeOwner ⟨6⟩ = ⟨0⟩ ∧
  owner ≠ 0 ∧ owner ≠ evm.executionEnv.codeOwner ∧
  evm.executionEnv.weiValue ≠ ⟨0⟩ ∧ depositExecutionCredit evm owner < wordLimit

theorem deposit_execution_next_eval (evm : Ethereum.State) (owner : Address) :
    evalExpr? config ⟨contract, depositLocals owner⟩
      (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨6⟩ ⟨1⟩)
      (.binary .add (.storage ⟨"pendingDeposits", [.mindex (.var "owner")]⟩) (.env .callvalue)) =
      .ok (.int (depositExecutionCredit evm owner)) := by
  have load := eval_pending (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨6⟩ ⟨1⟩)
    (depositLocals owner) owner (by simp [depositLocals]) (store_get_self _ _ _)
  rw [storageStore_executionEnv] at load
  simp [evalExpr?, load, EvalResult.bind, bind, pure, envValue,
    storageStore_executionEnv, evalBinaryOp?, depositExecutionCredit]
  rfl

/-- Every failed deposit check has a source execution that reverts. -/
theorem deposit_body_rejection (evm : Ethereum.State) (owner : Address)
    (reject : ¬ DepositExecutionChecks evm owner) :
    ExactBlock config ⟨contract, depositLocals owner⟩ evm contract.transitions[0]!.body .reverted := by
  by_cases unlocked : readWord evm evm.executionEnv.codeOwner ⟨6⟩ = ⟨0⟩
  · have lockGuard : evalExpr? config ⟨contract, depositLocals owner⟩ evm depositLockGuard =
        .ok (.bool true) := by simpa [unlocked] using deposit_lock_eval evm owner
    refine exact_cons (exact_require_true lockGuard) ?_
    refine exact_cons (exact_assign (value := .int 1) ?_
      (assign_entered evm (depositLocals owner) ⟨1⟩ (by simp [depositLocals]))) ?_
    · simp only [evalExpr?, pure]
    let locked := Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨6⟩ ⟨1⟩
    by_cases validOwner : owner ≠ 0 ∧ owner ≠ evm.executionEnv.codeOwner
    · have ownerGuard : evalExpr? config ⟨contract, depositLocals owner⟩ locked depositOwnerGuard =
          .ok (.bool true) := by
        simpa [locked, storageStore_executionEnv, validOwner] using deposit_owner_eval locked owner
      refine exact_cons (exact_require_true ownerGuard) ?_
      by_cases value : evm.executionEnv.weiValue ≠ ⟨0⟩
      · have valueGuard : evalExpr? config ⟨contract, depositLocals owner⟩ locked depositValueGuard =
            .ok (.bool true) := by
          simpa [locked, storageStore_executionEnv, value] using deposit_value_eval locked owner
        refine exact_cons (exact_require_true valueGuard) ?_
        refine exact_cons (exact_let (deposit_execution_next_eval evm owner)) ?_
        have overflow : ¬ depositExecutionCredit evm owner < wordLimit := by
          intro bound
          exact reject ⟨unlocked, validOwner.1, validOwner.2, value, bound⟩
        apply exact_require_false
        simpa [overflow] using deposit_range_eval locked owner (depositExecutionCredit evm owner)
      · apply exact_require_false
        simpa [locked, storageStore_executionEnv, value] using deposit_value_eval locked owner
    · apply exact_require_false
      simpa [locked, storageStore_executionEnv, validOwner] using deposit_owner_eval locked owner
  · apply exact_require_false
    simpa [unlocked] using deposit_lock_eval evm owner

end Rollup.EVM
