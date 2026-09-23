import proofs.BatchAuthorization
import proofs.Constructor

open Solm ABI Ethereum Reasoning.Theory

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Rollup.EVM

theorem eval_batch_number (evm : Ethereum.State) (locals : Store)
    (free : locals.get? "batchNumber" = none) :
    evalExpr? config ⟨contract, locals⟩ evm (.storage ⟨"batchNumber", []⟩) =
      .ok (.int (readWord evm evm.executionEnv.codeOwner ⟨2⟩).toNat) := by
  apply evalExpr_storage_scalar_value (er := ⟨"batchNumber", []⟩)
    (t := .int uint256) (loc := wordLoc ⟨2⟩) free
  · simp [evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind]
  · rfl
  · rfl
  · exact storageLocLoad_uint256 evm ⟨2⟩

theorem eval_batch_root (evm : Ethereum.State) (locals : Store)
    (free : locals.get? "stateRoot" = none) :
    evalExpr? config ⟨contract, locals⟩ evm (.storage ⟨"stateRoot", []⟩) =
      .ok (rootValue (readWord evm evm.executionEnv.codeOwner ⟨1⟩).val) := by
  apply evalExpr_storage_scalar_value (er := ⟨"stateRoot", []⟩)
    (t := .bytes ⟨31, by decide⟩) (loc := bytes32Loc ⟨1⟩) free
  · simp [evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind]
  · rfl
  · rfl
  · simpa [rootValue, toByteArray_eq_toBytesBE, byteArray_toList_eq] using
      storageLocLoad_bytes32 evm ⟨1⟩

def batchLockedState (evm : Ethereum.State) : Ethereum.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨6⟩ ⟨1⟩

def batchHeaderLocals (evm : Ethereum.State) (batch : Batch) : Store :=
  (batchLocals batch).insert "nextNumber"
    (.int ((readWord evm evm.executionEnv.codeOwner ⟨2⟩).toNat + 1))

/-- An accepted source batch uses the next bounded number and the current root. -/
theorem batch_source_header (evm out : Ethereum.State) (batch : Batch)
    (frame : Frame) (values : Option (List Value))
    (run : ExecTransitionBody config contract evm (batchLocals batch)
      contract.transitions[1]!.body (.returned frame out values)) :
    batch.number = (readWord evm evm.executionEnv.codeOwner ⟨2⟩).toNat + 1 ∧
    batch.number < wordLimit ∧
    batch.oldRoot = (readWord evm evm.executionEnv.codeOwner ⟨1⟩).val ∧
    ExecFuncBody config ⟨contract, batchHeaderLocals evm batch⟩ (batchLockedState evm)
      (contract.transitions[1]!.body.drop 8) (.returned frame out values) := by
  have afterPayment := (accepted_require run).2
  have afterGuard := (accepted_require afterPayment).2
  have afterLock := accepted_assign (value := .int 1) (by simp only [evalExpr?, pure])
    (assign_entered evm (batchLocals batch) ⟨1⟩ (by simp [batchLocals])) afterGuard
  have afterAuth := (accepted_require afterLock).2
  let locked := Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨6⟩ ⟨1⟩
  let next := (readWord evm evm.executionEnv.codeOwner ⟨2⟩).toNat + 1
  have sameNumber : readWord locked evm.executionEnv.codeOwner ⟨2⟩ =
      readWord evm evm.executionEnv.codeOwner ⟨2⟩ :=
    storageLoad_storageStore_ne evm _ (by decide)
  have loadNumber := eval_batch_number locked (batchLocals batch) (by simp [batchLocals])
  have evaluated : evalExpr? config ⟨contract, batchLocals batch⟩ locked
      (.binary .add (.storage ⟨"batchNumber", []⟩) (.intLit 1)) = .ok (.int next) := by
    simp only [evalExpr?, loadNumber, EvalResult.bind, bind, pure, evalBinaryOp?,
      locked, storageStore_executionEnv, sameNumber, next, Nat.cast_add, Nat.cast_one]
  let locals := (batchLocals batch).insert "nextNumber" (.int next)
  have nextArg : locals.get? "nextNumber" = some (.int next) := store_get_self _ _ _
  have numberArg : locals.get? "nextBatchNumber" = some (.int batch.number) := by
    dsimp only [locals, batchLocals]
    repeat rw [store_get_ne _ _ (by decide)]
    exact store_get_self _ _ _
  have oldRootArg : locals.get? "oldRoot" = some (rootValue batch.oldRoot) := by
    dsimp only [locals, batchLocals]
    repeat rw [store_get_ne _ _ (by decide)]
    exact store_get_self _ _ _
  have afterNumber := accepted_exact (exact_let evaluated) afterAuth
  obtain ⟨range, afterRange⟩ := accepted_require afterNumber
  obtain ⟨number, afterNumberCheck⟩ := accepted_require afterRange
  obtain ⟨root, remaining⟩ := accepted_require afterNumberCheck
  have numberEq : batch.number = next := by
    change evalExpr? config ⟨contract, locals⟩ locked
      (.binary .eq (.var "nextBatchNumber") (.var "nextNumber")) = .ok (.bool true) at number
    simp only [evalExpr?, numberArg, nextArg, EvalResult.ofOption,
      EvalResult.bind, bind, evalBinaryOp?] at number
    simpa using number
  have fits : next < wordLimit := by
    change evalExpr? config ⟨contract, locals⟩ locked
      (.binary .lt (.var "nextNumber") (.intLit (2 ^ 256))) = .ok (.bool true) at range
    simp only [evalExpr?, nextArg, EvalResult.ofOption, EvalResult.bind,
      bind, pure, evalBinaryOp?, EvalResult.ok.injEq, Value.bool.injEq, decide_eq_true_eq] at range
    exact_mod_cast range
  have rootLoad := eval_batch_root locked locals (by simp [locals, batchLocals])
  have sameRoot : readWord locked evm.executionEnv.codeOwner ⟨1⟩ =
      readWord evm evm.executionEnv.codeOwner ⟨1⟩ :=
    storageLoad_storageStore_ne evm _ (by decide)
  change evalExpr? config ⟨contract, locals⟩ locked
    (.binary .eq (.var "oldRoot") (.storage ⟨"stateRoot", []⟩)) = .ok (.bool true) at root
  have valuesEq : rootValue batch.oldRoot =
      rootValue (readWord evm evm.executionEnv.codeOwner ⟨1⟩).val := by
    simp only [evalExpr?, oldRootArg, rootLoad, rootValue,
      EvalResult.ofOption, EvalResult.bind, bind, evalBinaryOp?] at root
    have equalValues : rootValue batch.oldRoot =
        rootValue (readWord locked locked.executionEnv.codeOwner ⟨1⟩).val := by
      simpa only [rootValue, EvalResult.ok.injEq, Value.bool.injEq, beq_iff_eq] using root
    simpa only [locked, storageStore_executionEnv, sameRoot] using equalValues
  have words := congrArg valueToWord valuesEq
  rw [rootValue_word, rootValue_word] at words
  exact ⟨numberEq, numberEq.symm ▸ fits,
    congrArg UInt256.val (Option.some.inj words), remaining⟩

/-- Accepted source batches satisfy number and root continuity. -/
theorem batch_source_continuity (evm out : Ethereum.State) (batch : Batch)
    (frame : Frame) (values : Option (List Value))
    (run : ExecTransitionBody config contract evm (batchLocals batch)
      contract.transitions[1]!.body (.returned frame out values)) :
    batch.number = (readWord evm evm.executionEnv.codeOwner ⟨2⟩).toNat + 1 ∧
    batch.number < wordLimit ∧
    batch.oldRoot = (readWord evm evm.executionEnv.codeOwner ⟨1⟩).val := by
  have header := batch_source_header evm out batch frame values run
  exact ⟨header.1, header.2.1, header.2.2.1⟩

end Rollup.EVM
