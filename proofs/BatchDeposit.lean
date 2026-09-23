import proofs.BatchOwners
import proofs.BatchStorage

open Solm ABI Ethereum Reasoning.Theory

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Rollup.EVM

def batchDepositCredit (evm : Ethereum.State) (batch : Batch) : Nat :=
  (readWord (batchLockedState evm) evm.executionEnv.codeOwner
    (keySlot (.pending batch.depositOwner))).toNat

def batchDepositLocals (evm : Ethereum.State) (batch : Batch) : Store :=
  (batchHeaderLocals evm batch).insert "depositCredit" (.int (batchDepositCredit evm batch))

def batchDebitedState (evm : Ethereum.State) (batch : Batch) : Ethereum.State :=
  Solm.EVM.storageStore (batchLockedState evm) evm.executionEnv.codeOwner
    (keySlot (.pending batch.depositOwner))
    (UInt256.ofNat (batchDepositCredit evm batch - batch.depositAmount))

/-- The batch consumes no more than the credit read after the lock write. -/
theorem batch_source_after_deposit (evm out : Ethereum.State) (batch : Batch)
    (frame : Frame) (values : Option (List Value)) (keys : AccessScope)
    (run : ExecTransitionBody config contract evm (batchLocals batch)
      contract.transitions[1]!.body (.returned frame out values)) :
    batch.depositAmount ≤ batchDepositCredit evm batch ∧
    ExecFuncBody config ⟨contract, batchDepositLocals evm batch⟩ (batchDebitedState evm batch)
      (contract.transitions[1]!.body.drop 13) (.returned frame out values) := by
  have afterOwners := (batch_source_after_owners evm out batch frame values keys run).2.2
  have ownerArg : (batchHeaderLocals evm batch).get? "depositOwner" =
      some (.address batch.depositOwner) := by
    dsimp only [batchHeaderLocals, batchLocals]
    repeat rw [store_get_ne _ _ (by decide)]
    exact store_get_self _ _ _
  have lockedEnv : (batchLockedState evm).executionEnv = evm.executionEnv := storageStore_executionEnv ..
  have load := eval_batch_pending (batchLockedState evm) (batchHeaderLocals evm batch)
    batch.depositOwner (by simp [batchHeaderLocals, batchLocals]) ownerArg
  rw [lockedEnv] at load
  change evalExpr? config ⟨contract, batchHeaderLocals evm batch⟩ (batchLockedState evm)
    (.storage ⟨"pendingDeposits", [.mindex (.var "depositOwner")]⟩) =
    .ok (.int (batchDepositCredit evm batch)) at load
  have afterRead := accepted_exact (exact_let load) afterOwners
  obtain ⟨checked, afterCheck⟩ := accepted_require afterRead
  have amountArg : (batchDepositLocals evm batch).get? "depositAmount" =
      some (.int batch.depositAmount) := by
    dsimp only [batchDepositLocals, batchHeaderLocals, batchLocals]
    repeat rw [store_get_ne _ _ (by decide)]
    exact store_get_self _ _ _
  have creditArg : (batchDepositLocals evm batch).get? "depositCredit" =
      some (.int (batchDepositCredit evm batch)) := store_get_self _ _ _
  have allowed : batch.depositAmount ≤ batchDepositCredit evm batch := by
    change evalExpr? config ⟨contract, batchDepositLocals evm batch⟩ (batchLockedState evm)
      (.binary .le (.var "depositAmount") (.var "depositCredit")) = .ok (.bool true) at checked
    simp only [evalExpr?, amountArg, creditArg, EvalResult.ofOption, EvalResult.bind,
      bind, evalBinaryOp?] at checked
    simpa using checked
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
  rw [remainingWord, lockedEnv] at assign
  have subtract : evalExpr? config ⟨contract, batchDepositLocals evm batch⟩ (batchLockedState evm)
      (.binary .sub (.var "depositCredit") (.var "depositAmount")) =
      .ok (.int (Int.ofNat (batchDepositCredit evm batch - batch.depositAmount))) := by
    simp only [evalExpr?, creditArg, amountArg, EvalResult.ofOption, EvalResult.bind,
      bind, evalBinaryOp?]
    exact congrArg (fun value => EvalResult.ok (Value.int value)) (Int.ofNat_sub allowed).symm
  exact ⟨allowed, accepted_assign subtract assign afterCheck⟩

end Rollup.EVM
