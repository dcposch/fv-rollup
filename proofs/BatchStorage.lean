import proofs.SourceStorage

open Solm ABI Ethereum Reasoning.Theory

namespace Rollup.EVM

theorem eval_batch_pending (evm : Ethereum.State) (locals : Store) (owner : Address)
    (free : locals.get? "pendingDeposits" = none)
    (arg : locals.get? "depositOwner" = some (.address owner)) :
    evalExpr? config ⟨contract, locals⟩ evm
      (.storage ⟨"pendingDeposits", [.mindex (.var "depositOwner")]⟩) =
      .ok (.int (readWord evm evm.executionEnv.codeOwner (keySlot (.pending owner))).toNat) := by
  apply evalExpr_storage_scalar_value (er := ⟨"pendingDeposits", [.mindex (.address owner)]⟩)
    (t := .int uint256) (loc := wordLoc (keySlot (.pending owner))) free
  · simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, evalExpr?, arg,
      EvalResult.ofOption, EvalResult.bind, pure, bind, valueToKey?]
  · rfl
  · rfl
  · exact storageLocLoad_uint256 evm _

theorem assign_batch_pending (evm : Ethereum.State) (locals : Store) (owner : Address) (value : UInt256)
    (free : locals.get? "pendingDeposits" = none)
    (arg : locals.get? "depositOwner" = some (.address owner)) :
    assignStorageRef? config ⟨contract, locals⟩ evm .storage
      ⟨"pendingDeposits", [.mindex (.var "depositOwner")]⟩ (.int value.toNat) =
      .ok (⟨contract, locals⟩,
        Solm.EVM.storageStore evm evm.executionEnv.codeOwner (keySlot (.pending owner)) value) := by
  apply assignStorageRef_storage_scalar (er := ⟨"pendingDeposits", [.mindex (.address owner)]⟩)
    (loc := wordLoc (keySlot (.pending owner))) free
  · simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, evalExpr?, arg,
      EvalResult.ofOption, EvalResult.bind, pure, bind, valueToKey?]
  · rfl
  · rfl
  · exact storageLocStore_uint256 evm _ value

theorem eval_batch_backing (evm : Ethereum.State) (locals : Store)
    (free : locals.get? "backing" = none) :
    evalExpr? config ⟨contract, locals⟩ evm (.storage ⟨"backing", []⟩) =
      .ok (.int (readWord evm evm.executionEnv.codeOwner ⟨3⟩).toNat) := by
  apply evalExpr_storage_scalar_value (er := ⟨"backing", []⟩)
    (t := .int uint256) (loc := wordLoc ⟨3⟩) free
  · simp [evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind]
  · rfl
  · rfl
  · exact storageLocLoad_uint256 evm ⟨3⟩

theorem assign_batch_backing (evm : Ethereum.State) (locals : Store) (value : UInt256)
    (free : locals.get? "backing" = none) :
    assignStorageRef? config ⟨contract, locals⟩ evm .storage ⟨"backing", []⟩
      (.int value.toNat) =
      .ok (⟨contract, locals⟩, Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨3⟩ value) := by
  apply assignStorageRef_storage_scalar (er := ⟨"backing", []⟩)
    (loc := wordLoc ⟨3⟩) free
  · simp [evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind]
  · rfl
  · rfl
  · exact storageLocStore_uint256 evm ⟨3⟩ value

end Rollup.EVM
