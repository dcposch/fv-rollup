import proofs.BatchDeposit

open Solm ABI Ethereum Reasoning.Theory

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Rollup.EVM

def batchAvailable (evm : Ethereum.State) (batch : Batch) : Nat :=
  (readWord (batchDebitedState evm batch) evm.executionEnv.codeOwner ⟨3⟩).toNat + batch.depositAmount

def batchBackingLocals (evm : Ethereum.State) (batch : Batch) : Store :=
  (batchDepositLocals evm batch).insert "available" (.int (batchAvailable evm batch))

def batchBackedState (evm : Ethereum.State) (batch : Batch) : Ethereum.State :=
  Solm.EVM.storageStore (batchDebitedState evm batch) evm.executionEnv.codeOwner ⟨3⟩
    (UInt256.ofNat (batchAvailable evm batch - batch.withdrawalAmount))

/-- A batch can withdraw only from its bounded available backing. -/
theorem batch_source_after_backing (evm out : Ethereum.State) (batch : Batch)
    (frame : Frame) (values : Option (List Value)) (keys : AccessScope)
    (run : ExecTransitionBody config contract evm (batchLocals batch)
      contract.transitions[1]!.body (.returned frame out values)) :
    batchAvailable evm batch < wordLimit ∧
    batch.withdrawalAmount ≤ batchAvailable evm batch ∧
    ExecFuncBody config ⟨contract, batchBackingLocals evm batch⟩ (batchBackedState evm batch)
      (contract.transitions[1]!.body.drop 17) (.returned frame out values) := by
  have afterDeposit := (batch_source_after_deposit evm out batch frame values keys run).2
  have env : (batchDebitedState evm batch).executionEnv = evm.executionEnv := by
    simp only [batchDebitedState, batchLockedState, storageStore_executionEnv]
  have depositArg : (batchDepositLocals evm batch).get? "depositAmount" =
      some (.int batch.depositAmount) := by
    dsimp only [batchDepositLocals, batchHeaderLocals, batchLocals]
    repeat rw [store_get_ne _ _ (by decide)]
    exact store_get_self _ _ _
  have load := eval_batch_backing (batchDebitedState evm batch) (batchDepositLocals evm batch)
    (by simp [batchDepositLocals, batchHeaderLocals, batchLocals])
  have add : evalExpr? config ⟨contract, batchDepositLocals evm batch⟩ (batchDebitedState evm batch)
      (.binary .add (.storage ⟨"backing", []⟩) (.var "depositAmount")) =
      .ok (.int (batchAvailable evm batch)) := by
    simp only [evalExpr?, load, depositArg, EvalResult.ofOption, EvalResult.bind,
      bind, evalBinaryOp?, env, batchAvailable, Nat.cast_add]
  have afterAdd := accepted_exact (exact_let add) afterDeposit
  obtain ⟨range, afterRange⟩ := accepted_require afterAdd
  obtain ⟨checked, afterCheck⟩ := accepted_require afterRange
  have availableArg : (batchBackingLocals evm batch).get? "available" =
      some (.int (batchAvailable evm batch)) := store_get_self _ _ _
  have withdrawalArg : (batchBackingLocals evm batch).get? "withdrawalAmount" =
      some (.int batch.withdrawalAmount) := by
    dsimp only [batchBackingLocals, batchDepositLocals, batchHeaderLocals, batchLocals]
    repeat rw [store_get_ne _ _ (by decide)]
    exact store_get_self _ _ _
  have fits : batchAvailable evm batch < wordLimit := by
    change evalExpr? config ⟨contract, batchBackingLocals evm batch⟩ (batchDebitedState evm batch)
      (.binary .lt (.var "available") (.intLit (2 ^ 256))) = .ok (.bool true) at range
    simp only [evalExpr?, availableArg, EvalResult.ofOption, EvalResult.bind, bind, pure,
      evalBinaryOp?, EvalResult.ok.injEq, Value.bool.injEq, decide_eq_true_eq] at range
    exact_mod_cast range
  have allowed : batch.withdrawalAmount ≤ batchAvailable evm batch := by
    change evalExpr? config ⟨contract, batchBackingLocals evm batch⟩ (batchDebitedState evm batch)
      (.binary .le (.var "withdrawalAmount") (.var "available")) = .ok (.bool true) at checked
    simp only [evalExpr?, withdrawalArg, availableArg, EvalResult.ofOption,
      EvalResult.bind, bind, evalBinaryOp?] at checked
    simpa using checked
  have remainderBound : batchAvailable evm batch - batch.withdrawalAmount < wordLimit :=
    lt_of_le_of_lt (Nat.sub_le _ _) fits
  have remainderWord : (UInt256.ofNat (batchAvailable evm batch - batch.withdrawalAmount)).toNat =
      batchAvailable evm batch - batch.withdrawalAmount := ulit_toNat' _ remainderBound
  have assign := assign_batch_backing (batchDebitedState evm batch) (batchBackingLocals evm batch)
    (UInt256.ofNat (batchAvailable evm batch - batch.withdrawalAmount))
    (by simp [batchBackingLocals, batchDepositLocals, batchHeaderLocals, batchLocals])
  rw [remainderWord, env] at assign
  have subtract : evalExpr? config ⟨contract, batchBackingLocals evm batch⟩ (batchDebitedState evm batch)
      (.binary .sub (.var "available") (.var "withdrawalAmount")) =
      .ok (.int (Int.ofNat (batchAvailable evm batch - batch.withdrawalAmount))) := by
    simp only [evalExpr?, availableArg, withdrawalArg, EvalResult.ofOption,
      EvalResult.bind, bind, evalBinaryOp?]
    exact congrArg (fun value => EvalResult.ok (Value.int value)) (Int.ofNat_sub allowed).symm
  exact ⟨fits, allowed, accepted_assign subtract assign afterCheck⟩

end Rollup.EVM
