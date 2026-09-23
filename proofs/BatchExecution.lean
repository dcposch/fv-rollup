import proofs.BatchClaims
import proofs.BatchFinalStorage

open Solm ABI Ethereum Reasoning.Theory

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Rollup.EVM

def batchRootedState (evm : Ethereum.State) (batch : Batch) : Ethereum.State :=
  Solm.EVM.storageStore (batchCreditedState evm batch) evm.executionEnv.codeOwner ⟨1⟩ ⟨batch.newRoot⟩

def batchNumberedState (evm : Ethereum.State) (batch : Batch) : Ethereum.State :=
  Solm.EVM.storageStore (batchRootedState evm batch) evm.executionEnv.codeOwner ⟨2⟩
    (UInt256.ofNat batch.number)

def batchExecutionState (evm : Ethereum.State) (batch : Batch) : Ethereum.State :=
  Solm.EVM.storageStore (batchNumberedState evm batch) evm.executionEnv.codeOwner ⟨6⟩ ⟨0⟩

/-- Every accepted source batch has these exact writes and returns no value. -/
theorem batch_source_exact (evm out : Ethereum.State) (batch : Batch)
    (frame : Frame) (values : Option (List Value)) (keys : AccessScope)
    (run : ExecTransitionBody config contract evm (batchLocals batch)
      contract.transitions[1]!.body (.returned frame out values)) :
    out = batchExecutionState evm batch ∧
    frame = ⟨contract, batchClaimLocals evm batch⟩ ∧ values = none := by
  have afterClaims := (batch_source_after_claims evm out batch frame values keys run).2
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
  have afterRoot := accepted_assign rootEval rootAssign afterClaims
  have numberEval : evalExpr? config ⟨contract, batchClaimLocals evm batch⟩ (batchRootedState evm batch)
      (.var "nextBatchNumber") = .ok (.int batch.number) := by
    simp only [evalExpr?, numberArg, EvalResult.ofOption]
  have numberBound := (batch_source_continuity evm out batch frame values run).2.1
  have numberAssign := assign_batch_number (batchRootedState evm batch) (batchClaimLocals evm batch)
    (UInt256.ofNat batch.number) (by simp [batchClaimLocals, batchBackingLocals, batchDepositLocals,
      batchHeaderLocals, batchLocals])
  rw [ulit_toNat' _ numberBound, rootedEnv] at numberAssign
  have afterNumber := accepted_assign numberEval numberAssign afterRoot
  have unlock := assign_entered (batchNumberedState evm batch) (batchClaimLocals evm batch) ⟨0⟩
    (by simp [batchClaimLocals, batchBackingLocals, batchDepositLocals, batchHeaderLocals, batchLocals])
  rw [numberedEnv] at unlock
  have finished := accepted_assign (value := .int 0) (by simp only [evalExpr?, pure]) unlock afterNumber
  have exactEnd := (exact_function (exact_nil config ⟨contract, batchClaimLocals evm batch⟩
    (batchExecutionState evm batch))).2 _ finished
  cases exactEnd
  exact ⟨rfl, rfl, rfl⟩

end Rollup.EVM
