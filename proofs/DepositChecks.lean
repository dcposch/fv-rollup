import proofs.Deposit

open Solm ABI Ethereum Reasoning.Theory

namespace Rollup.EVM

def depositLockGuard : Expr := .binary .eq (.storage ⟨"entered", []⟩) (.intLit 0)
def depositOwnerGuard : Expr :=
  .binary .and
    (.binary .ne (.var "owner") (.cast (.intLit 0) (.elem .address)))
    (.binary .ne (.var "owner") (.env .this))
def depositValueGuard : Expr := .binary .ne (.env .callvalue) (.intLit 0)
def depositRangeGuard : Expr := .binary .lt (.var "nextCredit") (.intLit (2 ^ 256))

def DepositChecks (evm : Ethereum.State) (owner : Address) : Prop :=
  readWord evm evm.executionEnv.codeOwner ⟨6⟩ = ⟨0⟩ ∧
  owner ≠ 0 ∧ owner ≠ evm.executionEnv.codeOwner ∧
  evm.executionEnv.weiValue ≠ ⟨0⟩ ∧ nextDepositCredit evm owner < wordLimit

theorem deposit_lock_eval (evm : Ethereum.State) (owner : Address) :
    evalExpr? config ⟨contract, depositLocals owner⟩ evm depositLockGuard =
      .ok (.bool (decide (readWord evm evm.executionEnv.codeOwner ⟨6⟩ = ⟨0⟩))) := by
  have load := eval_entered evm (depositLocals owner) (by simp [depositLocals])
  simp only [depositLockGuard, evalExpr?, load, bind, EvalResult.bind, pure, evalBinaryOp?]
  congr 2
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, Value.int.injEq, decide_eq_true_eq]
  constructor
  · intro zero
    exact uint256_toNat_eq_zero (Int.ofNat.inj zero)
  · intro zero
    rw [zero]
    rfl

theorem deposit_owner_eval (evm : Ethereum.State) (owner : Address) :
    evalExpr? config ⟨contract, depositLocals owner⟩ evm depositOwnerGuard =
      .ok (.bool (decide (owner ≠ 0 ∧ owner ≠ evm.executionEnv.codeOwner))) := by
  have arg : (depositLocals owner).get? "owner" = some (.address owner) := store_get_self _ _ _
  simp only [depositOwnerGuard, evalExpr?, arg, EvalResult.ofOption, EvalResult.bind, bind, pure,
    evalBinaryOp?, castValue?, envValue, Int.lt_irrefl, ↓reduceIte, Int.toNat_zero]
  by_cases zero : owner = 0
  · subst owner
    simp [show AccountAddress.ofNat 0 = (0 : Address) from rfl]
  · have nonzero : (Value.address owner == Value.address (AccountAddress.ofNat 0)) = false := by
      apply beq_eq_false_iff_ne.mpr
      simpa using zero
    simp only [nonzero, Bool.not_false]
    by_cases self : owner = evm.executionEnv.codeOwner
    · subst owner
      simp
    · have different : (Value.address owner == Value.address evm.executionEnv.codeOwner) = false := by
        apply beq_eq_false_iff_ne.mpr
        simpa using self
      simp [different, self, zero]

theorem deposit_value_eval (evm : Ethereum.State) (owner : Address) :
    evalExpr? config ⟨contract, depositLocals owner⟩ evm depositValueGuard =
      .ok (.bool (decide (evm.executionEnv.weiValue ≠ ⟨0⟩))) := by
  simp only [depositValueGuard, evalExpr?, EvalResult.bind, bind, pure, envValue, evalBinaryOp?]
  by_cases zero : evm.executionEnv.weiValue = ⟨0⟩
  · simp [zero]
  · have different : (Value.int (Int.ofNat evm.executionEnv.weiValue.toNat) == Value.int 0) = false := by
      apply beq_eq_false_iff_ne.mpr
      intro same
      exact zero (uint256_toNat_eq_zero (Int.ofNat.inj (Value.int.inj same)))
    change EvalResult.ok (Value.bool (!(Value.int (Int.ofNat evm.executionEnv.weiValue.toNat) == .int 0))) = _
    simp only [different, Bool.not_false, decide_eq_true zero]

theorem deposit_range_eval (evm : Ethereum.State) (owner : Address) (next : Nat) :
    evalExpr? config ⟨contract, (depositLocals owner).insert "nextCredit" (.int next)⟩ evm
      depositRangeGuard = .ok (.bool (decide (next < wordLimit))) := by
  simp only [depositRangeGuard, evalExpr?, store_get_self, EvalResult.ofOption,
    EvalResult.bind, bind, pure, evalBinaryOp?]
  have comparison : ((next : Int) < 2 ^ 256) = (next < wordLimit) := by
    apply propext
    change (next : Int) < Int.ofNat wordLimit ↔ next < wordLimit
    exact Int.ofNat_lt
  apply congrArg EvalResult.ok
  apply congrArg Value.bool
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  exact Iff.of_eq comparison

theorem deposit_next_eval (evm : Ethereum.State) (owner : Address)
    (separate : keySlot (.pending owner) ≠ ⟨6⟩) :
    evalExpr? config ⟨contract, depositLocals owner⟩
      (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨6⟩ ⟨1⟩)
      (.binary .add (.storage ⟨"pendingDeposits", [.mindex (.var "owner")]⟩) (.env .callvalue)) =
      .ok (.int (nextDepositCredit evm owner)) := by
  have load := eval_pending (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨6⟩ ⟨1⟩)
    (depositLocals owner) owner (by simp [depositLocals]) (store_get_self _ _ _)
  rw [storageStore_executionEnv] at load
  have unchanged : readWord (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨6⟩ ⟨1⟩)
      evm.executionEnv.codeOwner (keySlot (.pending owner)) =
      readWord evm evm.executionEnv.codeOwner (keySlot (.pending owner)) :=
    storageLoad_storageStore_ne evm _ separate
  rw [unchanged] at load
  simp [evalExpr?, load, EvalResult.bind, bind, pure, envValue,
    storageStore_executionEnv, evalBinaryOp?, nextDepositCredit]
  rfl

/-- Every failed deposit check has a source execution that reverts. -/
theorem deposit_rejection_exact (evm : Ethereum.State) (owner : Address)
    (separate : keySlot (.pending owner) ≠ ⟨6⟩) (reject : ¬ DepositChecks evm owner) :
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
        refine exact_cons (exact_let (deposit_next_eval evm owner separate)) ?_
        have overflow : ¬ nextDepositCredit evm owner < wordLimit := by
          intro bound
          exact reject ⟨unlocked, validOwner.1, validOwner.2, value, bound⟩
        apply exact_require_false
        simpa [overflow] using deposit_range_eval locked owner (nextDepositCredit evm owner)
      · apply exact_require_false
        simpa [locked, storageStore_executionEnv, value] using deposit_value_eval locked owner
    · apply exact_require_false
      simpa [locked, storageStore_executionEnv, validOwner] using deposit_owner_eval locked owner
  · apply exact_require_false
    simpa [unlocked] using deposit_lock_eval evm owner

/-- Classify every deposit source execution, including all rejection paths. -/
theorem deposit_source_classification (evm : Ethereum.State) (owner : Address)
    (separate : keySlot (.pending owner) ≠ ⟨6⟩) :
    (DepositChecks evm owner ∧
      ExecTransitionBody config contract evm (depositLocals owner) contract.transitions[0]!.body
        (.returned ⟨contract, (depositLocals owner).insert "nextCredit" (.int (nextDepositCredit evm owner))⟩
          (depositState evm owner) none) ∧
      ∀ result, ExecTransitionBody config contract evm (depositLocals owner) contract.transitions[0]!.body result →
        result = .returned ⟨contract, (depositLocals owner).insert "nextCredit" (.int (nextDepositCredit evm owner))⟩
          (depositState evm owner) none) ∨
    (¬ DepositChecks evm owner ∧
      ExecTransitionBody config contract evm (depositLocals owner) contract.transitions[0]!.body .reverted ∧
      ∀ result, ExecTransitionBody config contract evm (depositLocals owner) contract.transitions[0]!.body result →
        result = .reverted) := by
  classical
  by_cases checks : DepositChecks evm owner
  · exact .inl ⟨checks, exact_function (deposit_source_exact evm owner checks.1 checks.2.1
      checks.2.2.1 checks.2.2.2.1 separate checks.2.2.2.2)⟩
  · exact .inr ⟨checks, exact_function_revert (deposit_rejection_exact evm owner separate checks)⟩

theorem deposit_success_checks (evm out : Ethereum.State) (owner : Address) (frame : Frame)
    (values : Option (List Value)) (separate : keySlot (.pending owner) ≠ ⟨6⟩)
    (run : ExecTransitionBody config contract evm (depositLocals owner) contract.transitions[0]!.body
      (.returned frame out values)) :
    DepositChecks evm owner ∧ out = depositState evm owner ∧ values = none := by
  rcases deposit_source_classification evm owner separate with ⟨checks, _, unique⟩ | ⟨_, _, unique⟩
  · have same := ExecResult.returned.inj (unique _ run)
    exact ⟨checks, same.2.1, same.2.2⟩
  · have impossible := unique _ run
    cases impossible

end Rollup.EVM
