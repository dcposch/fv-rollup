import proofs.SourceStorage

open Solm ABI Ethereum Reasoning.Theory

namespace Rollup.EVM

theorem eval_batch_claims (evm : Ethereum.State) (locals : Store) (owner : Address)
    (free : locals.get? "pendingWithdrawals" = none)
    (arg : locals.get? "withdrawalOwner" = some (.address owner)) :
    evalExpr? config ⟨contract, locals⟩ evm
      (.storage ⟨"pendingWithdrawals", [.mindex (.var "withdrawalOwner")]⟩) =
      .ok (.int (readWord evm evm.executionEnv.codeOwner (keySlot (.claims owner))).toNat) := by
  apply evalExpr_storage_scalar_value (er := ⟨"pendingWithdrawals", [.mindex (.address owner)]⟩)
    (t := .int uint256) (loc := wordLoc (keySlot (.claims owner))) free
  · simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, evalExpr?, arg,
      EvalResult.ofOption, EvalResult.bind, pure, bind, valueToKey?]
  · rfl
  · rfl
  · exact storageLocLoad_uint256 evm _

theorem assign_batch_claims (evm : Ethereum.State) (locals : Store) (owner : Address) (value : UInt256)
    (free : locals.get? "pendingWithdrawals" = none)
    (arg : locals.get? "withdrawalOwner" = some (.address owner)) :
    assignStorageRef? config ⟨contract, locals⟩ evm .storage
      ⟨"pendingWithdrawals", [.mindex (.var "withdrawalOwner")]⟩ (.int value.toNat) =
      .ok (⟨contract, locals⟩,
        Solm.EVM.storageStore evm evm.executionEnv.codeOwner (keySlot (.claims owner)) value) := by
  apply assignStorageRef_storage_scalar (er := ⟨"pendingWithdrawals", [.mindex (.address owner)]⟩)
    (loc := wordLoc (keySlot (.claims owner))) free
  · simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, evalExpr?, arg,
      EvalResult.ofOption, EvalResult.bind, pure, bind, valueToKey?]
  · rfl
  · rfl
  · exact storageLocStore_uint256 evm _ value

end Rollup.EVM
