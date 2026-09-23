import semantics.Storage
import Reasoning.SolmBody
import Reasoning.Storage

open Solm ABI Ethereum Reasoning.Theory

namespace Rollup.EVM

theorem eval_entered (evm : Ethereum.State) (locals : Store)
    (free : locals.get? "entered" = none) :
    evalExpr? config ⟨contract, locals⟩ evm (.storage ⟨"entered", []⟩) =
      .ok (.int (readWord evm evm.executionEnv.codeOwner ⟨6⟩).toNat) := by
  apply evalExpr_storage_scalar_value (er := ⟨"entered", []⟩)
    (t := .int uint256) (loc := wordLoc ⟨6⟩) free
  · simp [evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind]
  · rfl
  · rfl
  · exact storageLocLoad_uint256 evm ⟨6⟩

theorem assign_entered (evm : Ethereum.State) (locals : Store) (value : UInt256)
    (free : locals.get? "entered" = none) :
    assignStorageRef? config ⟨contract, locals⟩ evm .storage ⟨"entered", []⟩
      (.int value.toNat) =
      .ok (⟨contract, locals⟩, Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨6⟩ value) := by
  apply assignStorageRef_storage_scalar (er := ⟨"entered", []⟩)
    (loc := wordLoc ⟨6⟩) free
  · simp [evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind]
  · rfl
  · rfl
  · exact storageLocStore_uint256 evm ⟨6⟩ value

theorem pending_reference (evm : Ethereum.State) (locals : Store) (owner : Address)
    (arg : locals.get? "owner" = some (.address owner)) :
    evalStorageRef config ⟨contract, locals⟩ evm
      ⟨"pendingDeposits", [.mindex (.var "owner")]⟩ =
      .ok ⟨"pendingDeposits", [.mindex (.address owner)]⟩ := by
  simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, evalExpr?, arg, EvalResult.ofOption,
    EvalResult.bind, pure, bind, valueToKey?]

theorem eval_pending (evm : Ethereum.State) (locals : Store) (owner : Address)
    (free : locals.get? "pendingDeposits" = none)
    (arg : locals.get? "owner" = some (.address owner)) :
    evalExpr? config ⟨contract, locals⟩ evm
      (.storage ⟨"pendingDeposits", [.mindex (.var "owner")]⟩) =
      .ok (.int (readWord evm evm.executionEnv.codeOwner (keySlot (.pending owner))).toNat) := by
  apply evalExpr_storage_scalar_value (er := ⟨"pendingDeposits", [.mindex (.address owner)]⟩)
    (t := .int uint256) (loc := wordLoc (keySlot (.pending owner))) free
  · exact pending_reference evm locals owner arg
  · rfl
  · rfl
  · exact storageLocLoad_uint256 evm _

theorem assign_pending (evm : Ethereum.State) (locals : Store) (owner : Address) (value : UInt256)
    (free : locals.get? "pendingDeposits" = none)
    (arg : locals.get? "owner" = some (.address owner)) :
    assignStorageRef? config ⟨contract, locals⟩ evm .storage
      ⟨"pendingDeposits", [.mindex (.var "owner")]⟩ (.int value.toNat) =
      .ok (⟨contract, locals⟩,
        Solm.EVM.storageStore evm evm.executionEnv.codeOwner (keySlot (.pending owner)) value) := by
  apply assignStorageRef_storage_scalar (er := ⟨"pendingDeposits", [.mindex (.address owner)]⟩)
    (loc := wordLoc (keySlot (.pending owner))) free
  · exact pending_reference evm locals owner arg
  · rfl
  · rfl
  · exact storageLocStore_uint256 evm _ value

end Rollup.EVM
