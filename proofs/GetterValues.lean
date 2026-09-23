import proofs.GetterSource
import proofs.SourceStorage

open Solm ABI Ethereum Reasoning.Theory

namespace Rollup.EVM

def getterLocals : Getter → Store
  | .pendingDeposits owner | .pendingWithdrawals owner =>
      (∅ : Store).insert "owner" (.address owner)
  | _ => ∅

def getterExpression : Getter → Expr
  | .sequencer => .storage ⟨"sequencer", []⟩
  | .stateRoot => .storage ⟨"stateRoot", []⟩
  | .batchNumber => .storage ⟨"batchNumber", []⟩
  | .backing => .storage ⟨"backing", []⟩
  | .pendingDeposits _ => .storage ⟨"pendingDeposits", [.mindex (.var "owner")]⟩
  | .pendingWithdrawals _ => .storage ⟨"pendingWithdrawals", [.mindex (.var "owner")]⟩

def getterValue (evm : Ethereum.State) : Getter → Value
  | .sequencer => .address (AccountAddress.ofNat
      (UInt256.land (readWord evm evm.executionEnv.codeOwner ⟨0⟩) solcAddrMask).toNat)
  | .stateRoot => .fixedBytes ⟨31, by decide⟩
      (_root_.EVM.Word.toBytesBE (readWord evm evm.executionEnv.codeOwner ⟨1⟩))
  | .batchNumber => .int (readWord evm evm.executionEnv.codeOwner ⟨2⟩).toNat
  | .backing => .int (readWord evm evm.executionEnv.codeOwner ⟨3⟩).toNat
  | .pendingDeposits owner =>
      .int (readWord evm evm.executionEnv.codeOwner (keySlot (.pending owner))).toNat
  | .pendingWithdrawals owner =>
      .int (readWord evm evm.executionEnv.codeOwner (keySlot (.claims owner))).toNat

theorem getter_eval (evm : Ethereum.State) (getter : Getter) :
    evalExpr? config ⟨contract, getterLocals getter⟩ evm (getterExpression getter) =
      .ok (getterValue evm getter) := by
  cases getter with
  | sequencer =>
    apply evalExpr_storage_scalar_value (er := ⟨"sequencer", []⟩)
      (t := .address) (loc := addressOffset0Loc ⟨0⟩) (by simp [getterLocals])
    · simp [evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind]
    · rfl
    · rfl
    · exact storageLocLoad_address_offset0 evm ⟨0⟩
  | stateRoot =>
    apply evalExpr_storage_scalar_value (er := ⟨"stateRoot", []⟩)
      (t := .bytes ⟨31, by decide⟩) (loc := bytes32Loc ⟨1⟩) (by simp [getterLocals])
    · simp [evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind]
    · rfl
    · rfl
    · exact storageLocLoad_bytes32 evm ⟨1⟩
  | batchNumber =>
    apply evalExpr_storage_scalar_value (er := ⟨"batchNumber", []⟩)
      (t := .int uint256) (loc := wordLoc ⟨2⟩) (by simp [getterLocals])
    · simp [evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind]
    · rfl
    · rfl
    · exact storageLocLoad_uint256 evm ⟨2⟩
  | backing =>
    apply evalExpr_storage_scalar_value (er := ⟨"backing", []⟩)
      (t := .int uint256) (loc := wordLoc ⟨3⟩) (by simp [getterLocals])
    · simp [evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind]
    · rfl
    · rfl
    · exact storageLocLoad_uint256 evm ⟨3⟩
  | pendingDeposits owner =>
    exact eval_pending evm _ owner (by simp [getterLocals]) (by simp [getterLocals])
  | pendingWithdrawals owner =>
    apply evalExpr_storage_scalar_value (er := ⟨"pendingWithdrawals", [.mindex (.address owner)]⟩)
      (t := .int uint256) (loc := wordLoc (keySlot (.claims owner))) (by simp [getterLocals])
    · simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep,
        evalExpr?, getterLocals, EvalResult.ofOption, EvalResult.bind, pure, bind, valueToKey?]
    · rfl
    · rfl
    · exact storageLocLoad_uint256 evm _

private theorem exact_single_return {cfg frame evm expression value}
    (eval : evalExpr? cfg frame evm expression = .ok value) :
    ExactBlock cfg frame evm [.return [expression]] (.returned frame evm (some [value])) := by
  have values := evalExprs?_singleton eval
  refine ⟨.consReturn (.return values), ?_⟩
  intro other run
  cases run <;> cases_type ExecStmt <;> simp_all

/-- Each source getter returns its storage value and preserves the full state. -/
theorem getter_source_exact (evm : Ethereum.State) (getter : Getter)
    (nonpayable : evm.executionEnv.weiValue = ⟨0⟩) :
    let result := ExecResult.returned ⟨contract, getterLocals getter⟩ evm
      (some [getterValue evm getter])
    ExecTransitionBody config contract evm (getterLocals getter)
      (entryTransition (.read getter)).body result ∧
    ∀ other, ExecTransitionBody config contract evm (getterLocals getter)
      (entryTransition (.read getter)).body other → other = result := by
  have shape : (entryTransition (.read getter)).body =
      [.require (.binary .eq (.env .callvalue) (.intLit 0)), .return [getterExpression getter]] := by
    cases getter <;> rfl
  have body := exact_cons (exact_require_true (evalCallvalueEq_true nonpayable))
    (exact_single_return (getter_eval evm getter))
  rw [← shape] at body
  refine ⟨.execBlockRet body.run, ?_⟩
  intro other run
  cases run <;> rename_i block
  all_goals have same := body.unique _ block; cases same <;> rfl

end Rollup.EVM
