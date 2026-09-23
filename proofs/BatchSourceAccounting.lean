import proofs.BatchSourceOwners

open Solm ABI Ethereum Reasoning.Theory

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Rollup.EVM

/-- A covered deposit debit reaches the backing calculation. -/
theorem batch_deposit_success (evm : Ethereum.State) (batch : Batch)
    (checks : BatchExecutionChecks evm batch) :
    ExecBlock config ⟨contract, batchHeaderLocals evm batch⟩ (batchLockedState evm)
      ((contract.transitions[1]!.body.drop 10).take 3)
      (.ok ⟨contract, batchDepositLocals evm batch⟩ (batchDebitedState evm batch)) := by
  have ownerArg : (batchHeaderLocals evm batch).get? "depositOwner" =
      some (.address batch.depositOwner) := by
    dsimp only [batchHeaderLocals, batchLocals]
    repeat rw [store_get_ne _ _ (by decide)]
    exact store_get_self _ _ _
  have env : (batchLockedState evm).executionEnv = evm.executionEnv := storageStore_executionEnv ..
  have load := eval_batch_pending (batchLockedState evm) (batchHeaderLocals evm batch)
    batch.depositOwner (by simp [batchHeaderLocals, batchLocals]) ownerArg
  rw [env] at load
  change evalExpr? config ⟨contract, batchHeaderLocals evm batch⟩ (batchLockedState evm)
    (.storage ⟨"pendingDeposits", [.mindex (.var "depositOwner")]⟩) =
    .ok (.int (batchDepositCredit evm batch)) at load
  have amountArg : (batchDepositLocals evm batch).get? "depositAmount" =
      some (.int batch.depositAmount) := by
    dsimp only [batchDepositLocals, batchHeaderLocals, batchLocals]
    repeat rw [store_get_ne _ _ (by decide)]
    exact store_get_self _ _ _
  have creditArg : (batchDepositLocals evm batch).get? "depositCredit" =
      some (.int (batchDepositCredit evm batch)) := store_get_self _ _ _
  have guard : evalExpr? config ⟨contract, batchDepositLocals evm batch⟩ (batchLockedState evm)
      (.binary .le (.var "depositAmount") (.var "depositCredit")) = .ok (.bool true) := by
    have allowed : (batch.depositAmount : Int) ≤ batchDepositCredit evm batch := by
      exact_mod_cast checks.depositCovered
    simp only [evalExpr?, amountArg, creditArg, EvalResult.ofOption, EvalResult.bind,
      bind, evalBinaryOp?, decide_eq_true allowed]
  have remainingBound : batchDepositCredit evm batch - batch.depositAmount < wordLimit :=
    lt_of_le_of_lt (Nat.sub_le _ _) (readWord (batchLockedState evm)
      evm.executionEnv.codeOwner (keySlot (.pending batch.depositOwner))).val.isLt
  have remainingWord : (UInt256.ofNat (batchDepositCredit evm batch - batch.depositAmount)).toNat =
      batchDepositCredit evm batch - batch.depositAmount := ulit_toNat' _ remainingBound
  have ownerArg' : (batchDepositLocals evm batch).get? "depositOwner" =
      some (.address batch.depositOwner) := by
    rw [batchDepositLocals, store_get_ne _ _ (by decide)]
    exact ownerArg
  have assign := assign_batch_pending (batchLockedState evm) (batchDepositLocals evm batch)
    batch.depositOwner (UInt256.ofNat (batchDepositCredit evm batch - batch.depositAmount))
    (by simp [batchDepositLocals, batchHeaderLocals, batchLocals]) ownerArg'
  rw [remainingWord, env] at assign
  have subtract : evalExpr? config ⟨contract, batchDepositLocals evm batch⟩ (batchLockedState evm)
      (.binary .sub (.var "depositCredit") (.var "depositAmount")) =
      .ok (.int (Int.ofNat (batchDepositCredit evm batch - batch.depositAmount))) := by
    simp only [evalExpr?, creditArg, amountArg, EvalResult.ofOption, EvalResult.bind,
      bind, evalBinaryOp?]
    exact congrArg (fun value => EvalResult.ok (Value.int value)) (Int.ofNat_sub checks.depositCovered).symm
  exact .consNormal (.letDecl load) (.consNormal (.requireTrue guard)
    (.consNormal (.assign subtract assign) .nil))

/-- Bounded backing covers the withdrawal debit. -/
theorem batch_backing_success (evm : Ethereum.State) (batch : Batch)
    (checks : BatchExecutionChecks evm batch) :
    ExecBlock config ⟨contract, batchDepositLocals evm batch⟩ (batchDebitedState evm batch)
      ((contract.transitions[1]!.body.drop 13).take 4)
      (.ok ⟨contract, batchBackingLocals evm batch⟩ (batchBackedState evm batch)) := by
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
  have availableArg : (batchBackingLocals evm batch).get? "available" =
      some (.int (batchAvailable evm batch)) := store_get_self _ _ _
  have withdrawalArg : (batchBackingLocals evm batch).get? "withdrawalAmount" =
      some (.int batch.withdrawalAmount) := by
    dsimp only [batchBackingLocals, batchDepositLocals, batchHeaderLocals, batchLocals]
    repeat rw [store_get_ne _ _ (by decide)]
    exact store_get_self _ _ _
  have range : evalExpr? config ⟨contract, batchBackingLocals evm batch⟩ (batchDebitedState evm batch)
      (.binary .lt (.var "available") (.intLit (2 ^ 256))) = .ok (.bool true) := by
    have fits : (batchAvailable evm batch : Int) < 2 ^ 256 := by exact_mod_cast checks.backingFits
    simp only [evalExpr?, availableArg, EvalResult.ofOption, EvalResult.bind, bind, pure,
      evalBinaryOp?, decide_eq_true fits]
  have guard : evalExpr? config ⟨contract, batchBackingLocals evm batch⟩ (batchDebitedState evm batch)
      (.binary .le (.var "withdrawalAmount") (.var "available")) = .ok (.bool true) := by
    have allowed : (batch.withdrawalAmount : Int) ≤ batchAvailable evm batch := by
      exact_mod_cast checks.withdrawalCovered
    simp only [evalExpr?, withdrawalArg, availableArg, EvalResult.ofOption,
      EvalResult.bind, bind, evalBinaryOp?, decide_eq_true allowed]
  have remainderBound : batchAvailable evm batch - batch.withdrawalAmount < wordLimit :=
    lt_of_le_of_lt (Nat.sub_le _ _) checks.backingFits
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
    exact congrArg (fun value => EvalResult.ok (Value.int value)) (Int.ofNat_sub checks.withdrawalCovered).symm
  exact .consNormal (.letDecl add) (.consNormal (.requireTrue range)
    (.consNormal (.requireTrue guard) (.consNormal (.assign subtract assign) .nil)))

/-- A bounded claim update reaches the final root and number writes. -/
theorem batch_claims_success (evm : Ethereum.State) (batch : Batch)
    (checks : BatchExecutionChecks evm batch) :
    ExecBlock config ⟨contract, batchBackingLocals evm batch⟩ (batchBackedState evm batch)
      ((contract.transitions[1]!.body.drop 17).take 3)
      (.ok ⟨contract, batchClaimLocals evm batch⟩ (batchCreditedState evm batch)) := by
  have env : (batchBackedState evm batch).executionEnv = evm.executionEnv := by
    simp only [batchBackedState, batchDebitedState, batchLockedState, storageStore_executionEnv]
  have ownerArg : (batchBackingLocals evm batch).get? "withdrawalOwner" =
      some (.address batch.withdrawalOwner) := by
    dsimp only [batchBackingLocals, batchDepositLocals, batchHeaderLocals, batchLocals]
    repeat rw [store_get_ne _ _ (by decide)]
    exact store_get_self _ _ _
  have amountArg : (batchBackingLocals evm batch).get? "withdrawalAmount" =
      some (.int batch.withdrawalAmount) := by
    dsimp only [batchBackingLocals, batchDepositLocals, batchHeaderLocals, batchLocals]
    repeat rw [store_get_ne _ _ (by decide)]
    exact store_get_self _ _ _
  have load := eval_batch_claims (batchBackedState evm batch) (batchBackingLocals evm batch)
    batch.withdrawalOwner (by simp [batchBackingLocals, batchDepositLocals, batchHeaderLocals, batchLocals]) ownerArg
  have add : evalExpr? config ⟨contract, batchBackingLocals evm batch⟩ (batchBackedState evm batch)
      (.binary .add (.storage ⟨"pendingWithdrawals", [.mindex (.var "withdrawalOwner")]⟩)
        (.var "withdrawalAmount")) = .ok (.int (batchNextCredit evm batch)) := by
    simp only [evalExpr?, load, amountArg, EvalResult.ofOption, EvalResult.bind,
      bind, evalBinaryOp?, env, batchNextCredit, Nat.cast_add]
  have creditArg : (batchClaimLocals evm batch).get? "nextCredit" =
      some (.int (batchNextCredit evm batch)) := store_get_self _ _ _
  have range : evalExpr? config ⟨contract, batchClaimLocals evm batch⟩ (batchBackedState evm batch)
      (.binary .lt (.var "nextCredit") (.intLit (2 ^ 256))) = .ok (.bool true) := by
    have fits : (batchNextCredit evm batch : Int) < 2 ^ 256 := by exact_mod_cast checks.claimFits
    simp only [evalExpr?, creditArg, EvalResult.ofOption, EvalResult.bind, bind, pure,
      evalBinaryOp?, decide_eq_true fits]
  have ownerArg' : (batchClaimLocals evm batch).get? "withdrawalOwner" =
      some (.address batch.withdrawalOwner) := by
    rw [batchClaimLocals, store_get_ne _ _ (by decide)]
    exact ownerArg
  have assign := assign_batch_claims (batchBackedState evm batch) (batchClaimLocals evm batch)
    batch.withdrawalOwner (UInt256.ofNat (batchNextCredit evm batch))
    (by simp [batchClaimLocals, batchBackingLocals, batchDepositLocals, batchHeaderLocals, batchLocals]) ownerArg'
  rw [ulit_toNat' _ checks.claimFits, env] at assign
  have eval : evalExpr? config ⟨contract, batchClaimLocals evm batch⟩ (batchBackedState evm batch)
      (.var "nextCredit") = .ok (.int (batchNextCredit evm batch)) := by
    simp only [evalExpr?, creditArg, EvalResult.ofOption]
  exact .consNormal (.letDecl add) (.consNormal (.requireTrue range)
    (.consNormal (.assign eval assign) .nil))

end Rollup.EVM
