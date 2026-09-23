import proofs.BatchBacking
import proofs.BatchClaimStorage

open Solm ABI Ethereum Reasoning.Theory

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Rollup.EVM

def batchNextCredit (evm : Ethereum.State) (batch : Batch) : Nat :=
  (readWord (batchBackedState evm batch) evm.executionEnv.codeOwner
    (keySlot (.claims batch.withdrawalOwner))).toNat + batch.withdrawalAmount

def batchClaimLocals (evm : Ethereum.State) (batch : Batch) : Store :=
  (batchBackingLocals evm batch).insert "nextCredit" (.int (batchNextCredit evm batch))

def batchCreditedState (evm : Ethereum.State) (batch : Batch) : Ethereum.State :=
  Solm.EVM.storageStore (batchBackedState evm batch) evm.executionEnv.codeOwner
    (keySlot (.claims batch.withdrawalOwner)) (UInt256.ofNat (batchNextCredit evm batch))

/-- Accepted batches add withdrawal credit without word overflow. -/
theorem batch_source_after_claims (evm out : Ethereum.State) (batch : Batch)
    (frame : Frame) (values : Option (List Value)) (keys : AccessScope)
    (run : ExecTransitionBody config contract evm (batchLocals batch)
      contract.transitions[1]!.body (.returned frame out values)) :
    batchNextCredit evm batch < wordLimit ∧
    ExecFuncBody config ⟨contract, batchClaimLocals evm batch⟩ (batchCreditedState evm batch)
      (contract.transitions[1]!.body.drop 20) (.returned frame out values) := by
  have afterBacking := (batch_source_after_backing evm out batch frame values keys run).2.2
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
  have afterAdd := accepted_exact (exact_let add) afterBacking
  obtain ⟨range, afterRange⟩ := accepted_require afterAdd
  have creditArg : (batchClaimLocals evm batch).get? "nextCredit" =
      some (.int (batchNextCredit evm batch)) := store_get_self _ _ _
  have fits : batchNextCredit evm batch < wordLimit := by
    change evalExpr? config ⟨contract, batchClaimLocals evm batch⟩ (batchBackedState evm batch)
      (.binary .lt (.var "nextCredit") (.intLit (2 ^ 256))) = .ok (.bool true) at range
    simp only [evalExpr?, creditArg, EvalResult.ofOption, EvalResult.bind, bind, pure,
      evalBinaryOp?, EvalResult.ok.injEq, Value.bool.injEq, decide_eq_true_eq] at range
    exact_mod_cast range
  have ownerArg' : (batchClaimLocals evm batch).get? "withdrawalOwner" =
      some (.address batch.withdrawalOwner) := by
    rw [batchClaimLocals, store_get_ne _ _ (by decide)]
    exact ownerArg
  have assign := assign_batch_claims (batchBackedState evm batch) (batchClaimLocals evm batch)
    batch.withdrawalOwner (UInt256.ofNat (batchNextCredit evm batch))
    (by simp [batchClaimLocals, batchBackingLocals, batchDepositLocals, batchHeaderLocals, batchLocals]) ownerArg'
  rw [ulit_toNat' _ fits, env] at assign
  have eval : evalExpr? config ⟨contract, batchClaimLocals evm batch⟩ (batchBackedState evm batch)
      (.var "nextCredit") = .ok (.int (batchNextCredit evm batch)) := by
    simp only [evalExpr?, creditArg, EvalResult.ofOption]
  exact ⟨fits, accepted_assign eval assign afterRange⟩

end Rollup.EVM
