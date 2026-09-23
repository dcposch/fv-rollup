import proofs.SourceStorage
import proofs.SourceSteps
import proofs.SolmGuards
import proofs.GetterRefinement

open Solm ABI Ethereum Reasoning.Theory

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Rollup.EVM

theorem eval_batch_sequencer (evm : Ethereum.State) (locals : Store)
    (free : locals.get? "sequencer" = none) :
    evalExpr? config ⟨contract, locals⟩ evm (.storage ⟨"sequencer", []⟩) =
      .ok (getterValue evm .sequencer) := by
  apply evalExpr_storage_scalar_value (er := ⟨"sequencer", []⟩)
    (t := .address) (loc := addressOffset0Loc ⟨0⟩) free
  · simp [evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind]
  · rfl
  · rfl
  · exact storageLocLoad_address_offset0 evm ⟨0⟩

/-- An accepted source batch has zero call value and the stored sequencer as caller. -/
theorem batch_source_authorized (evm out : Ethereum.State) (locals : Store)
    (frame : Frame) (values : Option (List Value))
    (freeLock : locals.get? "entered" = none)
    (freeSequencer : locals.get? "sequencer" = none)
    (run : ExecTransitionBody config contract evm locals contract.transitions[1]!.body
      (.returned frame out values)) :
    evm.executionEnv.weiValue = ⟨0⟩ ∧
    Value.address evm.executionEnv.source = getterValue evm .sequencer := by
  obtain ⟨paid, afterPayment⟩ := accepted_require run
  have nonpayable : evm.executionEnv.weiValue = ⟨0⟩ := by
    by_contra nonzero
    have noValue := evalCallvalueEq_false (cfg := config) (solm := ⟨contract, locals⟩) nonzero
    rw [noValue] at paid
    cases paid
  obtain ⟨_, afterGuard⟩ := accepted_require afterPayment
  have afterLock := accepted_assign (value := .int 1) (by simp only [evalExpr?, pure])
    (assign_entered evm locals ⟨1⟩ freeLock) afterGuard
  have authorized := (accepted_require afterLock).1
  let locked := Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨6⟩ ⟨1⟩
  have load := eval_batch_sequencer locked locals freeSequencer
  change evalExpr? config ⟨contract, locals⟩ locked
    (.binary .eq (.env .caller) (.storage ⟨"sequencer", []⟩)) = .ok (.bool true) at authorized
  simp only [evalExpr?, load, getterValue, EvalResult.bind, bind, pure, envValue, evalBinaryOp?] at authorized
  have same : Value.address locked.executionEnv.source = getterValue locked .sequencer := by
    simpa only [getterValue, EvalResult.ok.injEq, Value.bool.injEq, beq_iff_eq] using authorized
  have unchanged : readWord locked evm.executionEnv.codeOwner ⟨0⟩ =
      readWord evm evm.executionEnv.codeOwner ⟨0⟩ :=
    storageLoad_storageStore_ne evm _ (by decide)
  refine ⟨nonpayable, ?_⟩
  simpa only [getterValue, locked, storageStore_executionEnv, unchanged] using same

def batchLocals (batch : Batch) : Store :=
  ((((((((∅ : Store).insert "nextBatchNumber" (.int batch.number)).insert
    "oldRoot" (rootValue batch.oldRoot)).insert
    "newRoot" (rootValue batch.newRoot)).insert
    "depositOwner" (.address batch.depositOwner)).insert
    "depositAmount" (.int batch.depositAmount)).insert
    "withdrawalOwner" (.address batch.withdrawalOwner)).insert
    "withdrawalAmount" (.int batch.withdrawalAmount))

/-- Bind source batch authorization to the call label. -/
theorem batch_source_call_authorized (evm out : Ethereum.State) (locals : Store)
    (frame : Frame) (values : Option (List Value))
    (caller : Address) (value : Nat) (batch : Batch) (keys : AccessScope)
    (bound : CallBound evm locals ⟨caller, value, .executeBatch batch⟩)
    (run : ExecTransitionBody config contract evm locals
      (entryTransition (.executeBatch batch)).body (.returned frame out values)) :
    caller = (project evm evm.executionEnv.codeOwner keys).sequencer ∧ value = 0 := by
  have binding : entryArgumentStore (.executeBatch batch) = some (batchLocals batch) := rfl
  have args := bound.2.2.2.2
  rw [binding] at args
  have sameLocals := Option.some.inj args
  subst locals
  have authorized := batch_source_authorized evm out (batchLocals batch) frame values
    (by simp [batchLocals]) (by simp [batchLocals]) run
  have modelReturn := getter_model_return evm .sequencer keys (by simp [entryKeys])
  change some [getterValue evm .sequencer] =
    some [Value.address (project evm evm.executionEnv.codeOwner keys).sequencer] at modelReturn
  have addressEq : evm.executionEnv.source =
      (project evm evm.executionEnv.codeOwner keys).sequencer := by
    rw [← authorized.2] at modelReturn
    simpa using modelReturn
  refine ⟨bound.1.trans addressEq, ?_⟩
  have valueEq : value = evm.executionEnv.weiValue.toNat := bound.2.1
  rw [valueEq, authorized.1]
  rfl

end Rollup.EVM
