import proofs.BatchSourceAccounting

open Solm ABI Ethereum Reasoning.Theory

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Rollup.EVM

/-- Complete the source batch by storing its root and number, then releasing the lock. -/
theorem batch_final_success (evm : Ethereum.State) (batch : Batch)
    (checks : BatchExecutionChecks evm batch) :
    ExecBlock config ⟨contract, batchClaimLocals evm batch⟩ (batchCreditedState evm batch)
      (contract.transitions[1]!.body.drop 20)
      (.ok ⟨contract, batchClaimLocals evm batch⟩ (batchExecutionState evm batch)) := by
  have creditedEnv : (batchCreditedState evm batch).executionEnv = evm.executionEnv := by
    simp only [batchCreditedState, batchBackedState, batchDebitedState,
      batchLockedState, storageStore_executionEnv]
  have rootedEnv : (batchRootedState evm batch).executionEnv = evm.executionEnv := by
    simp only [batchRootedState, storageStore_executionEnv, creditedEnv]
  have numberedEnv : (batchNumberedState evm batch).executionEnv = evm.executionEnv := by
    simp only [batchNumberedState, storageStore_executionEnv, rootedEnv]
  have rootArg : (batchClaimLocals evm batch).get? "newRoot" = some (rootValue batch.newRoot) := by
    dsimp only [batchClaimLocals, batchBackingLocals, batchDepositLocals, batchHeaderLocals, batchLocals]
    repeat rw [store_get_ne _ _ (by decide)]
    exact store_get_self _ _ _
  have numberArg : (batchClaimLocals evm batch).get? "nextBatchNumber" = some (.int batch.number) := by
    dsimp only [batchClaimLocals, batchBackingLocals, batchDepositLocals, batchHeaderLocals, batchLocals]
    repeat rw [store_get_ne _ _ (by decide)]
    exact store_get_self _ _ _
  have rootEval : evalExpr? config ⟨contract, batchClaimLocals evm batch⟩ (batchCreditedState evm batch)
      (.var "newRoot") = .ok (rootValue batch.newRoot) := by
    simp only [evalExpr?, rootArg, EvalResult.ofOption]
  have rootAssign := assign_batch_root (batchCreditedState evm batch) (batchClaimLocals evm batch)
    batch.newRoot (by simp [batchClaimLocals, batchBackingLocals, batchDepositLocals,
      batchHeaderLocals, batchLocals])
  rw [creditedEnv] at rootAssign
  have numberEval : evalExpr? config ⟨contract, batchClaimLocals evm batch⟩ (batchRootedState evm batch)
      (.var "nextBatchNumber") = .ok (.int batch.number) := by
    simp only [evalExpr?, numberArg, EvalResult.ofOption]
  have numberBound : batch.number < wordLimit := checks.nextNumber.symm ▸ checks.numberFits
  have numberAssign := assign_batch_number (batchRootedState evm batch) (batchClaimLocals evm batch)
    (UInt256.ofNat batch.number) (by simp [batchClaimLocals, batchBackingLocals, batchDepositLocals,
      batchHeaderLocals, batchLocals])
  rw [ulit_toNat' _ numberBound, rootedEnv] at numberAssign
  have unlock := assign_entered (batchNumberedState evm batch) (batchClaimLocals evm batch) ⟨0⟩
    (by simp [batchClaimLocals, batchBackingLocals, batchDepositLocals, batchHeaderLocals, batchLocals])
  rw [numberedEnv] at unlock
  exact .consNormal (.assign rootEval rootAssign) (.consNormal (.assign numberEval numberAssign)
    (.consNormal (.assign (by simp only [evalExpr?, pure]; rfl) unlock) .nil))

/-- All source checks construct an execution with the exact seven writes and no return value. -/
theorem batch_body_success (evm : Ethereum.State) (batch : Batch)
    (checks : BatchExecutionChecks evm batch) :
    ExecTransitionBody config contract evm (batchLocals batch) contract.transitions[1]!.body
      (.returned ⟨contract, batchClaimLocals evm batch⟩ (batchExecutionState evm batch) none) := by
  have blocks := execBlock_append (batch_header_success evm batch checks)
    (execBlock_append (batch_owners_success evm batch checks)
      (execBlock_append (batch_deposit_success evm batch checks)
        (execBlock_append (batch_backing_success evm batch checks)
          (execBlock_append (batch_claims_success evm batch checks) (batch_final_success evm batch checks)))))
  change ExecBlock config ⟨contract, batchLocals batch⟩ evm contract.transitions[1]!.body
    (.ok ⟨contract, batchClaimLocals evm batch⟩ (batchExecutionState evm batch)) at blocks
  exact .execBlockOK blocks

end Rollup.EVM
