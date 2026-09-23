import proofs.BatchExecution

open Solm ABI Ethereum Reasoning.Theory

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Rollup.EVM

/-- Source checks read each word at the point where the contract uses it. -/
structure BatchExecutionChecks (evm : Ethereum.State) (batch : Batch) : Prop where
  nonpayable : evm.executionEnv.weiValue = ⟨0⟩
  unlocked : readWord evm evm.executionEnv.codeOwner ⟨6⟩ = ⟨0⟩
  authorized : Value.address evm.executionEnv.source = getterValue evm .sequencer
  numberFits : (readWord evm evm.executionEnv.codeOwner ⟨2⟩).toNat + 1 < wordLimit
  nextNumber : batch.number = (readWord evm evm.executionEnv.codeOwner ⟨2⟩).toNat + 1
  oldRoot : batch.oldRoot = (readWord evm evm.executionEnv.codeOwner ⟨1⟩).val
  depositOwner : if batch.depositAmount = 0 then batch.depositOwner = 0
    else batch.depositOwner ≠ 0 ∧ batch.depositOwner ≠ evm.executionEnv.codeOwner
  withdrawalOwner : if batch.withdrawalAmount = 0 then batch.withdrawalOwner = 0
    else batch.withdrawalOwner ≠ 0 ∧ batch.withdrawalOwner ≠ evm.executionEnv.codeOwner
  depositCovered : batch.depositAmount ≤ batchDepositCredit evm batch
  backingFits : batchAvailable evm batch < wordLimit
  withdrawalCovered : batch.withdrawalAmount ≤ batchAvailable evm batch
  claimFits : batchNextCredit evm batch < wordLimit

/-- Valid source header checks reach the owner checks with the lock set. -/
theorem batch_header_success (evm : Ethereum.State) (batch : Batch)
    (checks : BatchExecutionChecks evm batch) :
    ExecBlock config ⟨contract, batchLocals batch⟩ evm
      (contract.transitions[1]!.body.take 8)
      (.ok ⟨contract, batchHeaderLocals evm batch⟩ (batchLockedState evm)) := by
  let locked := batchLockedState evm
  let next := (readWord evm evm.executionEnv.codeOwner ⟨2⟩).toNat + 1
  let locals := batchHeaderLocals evm batch
  have env : locked.executionEnv = evm.executionEnv := storageStore_executionEnv ..
  have lockEval := eval_entered evm (batchLocals batch) (by simp [batchLocals])
  rw [checks.unlocked] at lockEval
  have guard : evalExpr? config ⟨contract, batchLocals batch⟩ evm
      (.binary .eq (.storage ⟨"entered", []⟩) (.intLit 0)) = .ok (.bool true) := by
    simp only [evalExpr?, lockEval, bind, EvalResult.bind, pure, evalBinaryOp?]
    rfl
  have seqLoad := eval_batch_sequencer locked (batchLocals batch) (by simp [batchLocals])
  have sameSeq : getterValue locked .sequencer = getterValue evm .sequencer := by
    have sameWord : readWord locked evm.executionEnv.codeOwner ⟨0⟩ =
        readWord evm evm.executionEnv.codeOwner ⟨0⟩ :=
      storageLoad_storageStore_ne evm _ (by decide)
    simp only [getterValue, env, sameWord]
  have authorization : evalExpr? config ⟨contract, batchLocals batch⟩ locked
      (.binary .eq (.env .caller) (.storage ⟨"sequencer", []⟩)) = .ok (.bool true) := by
    simp only [evalExpr?, seqLoad, EvalResult.bind, bind, pure, envValue, env, sameSeq]
    rw [← checks.authorized]
    simp only [evalBinaryOp?, beq_self_eq_true]
  have sameNumber : readWord locked evm.executionEnv.codeOwner ⟨2⟩ =
      readWord evm evm.executionEnv.codeOwner ⟨2⟩ :=
    storageLoad_storageStore_ne evm _ (by decide)
  have numberLoad := eval_batch_number locked (batchLocals batch) (by simp [batchLocals])
  have nextEval : evalExpr? config ⟨contract, batchLocals batch⟩ locked
      (.binary .add (.storage ⟨"batchNumber", []⟩) (.intLit 1)) = .ok (.int next) := by
    simp only [evalExpr?, numberLoad, EvalResult.bind, bind, pure, evalBinaryOp?,
      env, sameNumber, next, Nat.cast_add, Nat.cast_one]
  have nextArg : locals.get? "nextNumber" = some (.int next) := store_get_self _ _ _
  have numberArg : locals.get? "nextBatchNumber" = some (.int batch.number) := by
    dsimp only [locals, batchHeaderLocals, batchLocals]
    repeat rw [store_get_ne _ _ (by decide)]
    exact store_get_self _ _ _
  have oldRootArg : locals.get? "oldRoot" = some (rootValue batch.oldRoot) := by
    dsimp only [locals, batchHeaderLocals, batchLocals]
    repeat rw [store_get_ne _ _ (by decide)]
    exact store_get_self _ _ _
  have range : evalExpr? config ⟨contract, locals⟩ locked
      (.binary .lt (.var "nextNumber") (.intLit (2 ^ 256))) = .ok (.bool true) := by
    have fits : (next : Int) < 2 ^ 256 := by exact_mod_cast checks.numberFits
    simp only [evalExpr?, nextArg, EvalResult.ofOption, EvalResult.bind,
      bind, pure, evalBinaryOp?, decide_eq_true fits]
  have number : evalExpr? config ⟨contract, locals⟩ locked
      (.binary .eq (.var "nextBatchNumber") (.var "nextNumber")) = .ok (.bool true) := by
    simp only [evalExpr?, numberArg, nextArg, EvalResult.ofOption,
      EvalResult.bind, bind, evalBinaryOp?, checks.nextNumber, next, beq_self_eq_true]
  have rootLoad := eval_batch_root locked locals (by simp [locals, batchHeaderLocals, batchLocals])
  have sameRoot : readWord locked evm.executionEnv.codeOwner ⟨1⟩ =
      readWord evm evm.executionEnv.codeOwner ⟨1⟩ :=
    storageLoad_storageStore_ne evm _ (by decide)
  have root : evalExpr? config ⟨contract, locals⟩ locked
      (.binary .eq (.var "oldRoot") (.storage ⟨"stateRoot", []⟩)) = .ok (.bool true) := by
    simp only [evalExpr?, oldRootArg, rootLoad, EvalResult.ofOption, EvalResult.bind,
      bind, env, sameRoot, checks.oldRoot]
    simp only [rootValue, evalBinaryOp?, beq_self_eq_true]
  refine .consNormal (.requireTrue (evalCallvalueEq_true checks.nonpayable)) ?_
  refine .consNormal (.requireTrue guard) ?_
  refine .consNormal (.assign (by simp only [evalExpr?, pure]; rfl)
    (assign_entered evm (batchLocals batch) ⟨1⟩ (by simp [batchLocals]))) ?_
  refine .consNormal (.requireTrue authorization) ?_
  refine .consNormal (.letDecl nextEval) ?_
  refine .consNormal (.requireTrue range) ?_
  refine .consNormal (.requireTrue number) ?_
  exact .consNormal (.requireTrue root) .nil

end Rollup.EVM
