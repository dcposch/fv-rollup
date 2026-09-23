import proofs.Constructor

open Solm ABI Ethereum Reasoning.Theory

namespace Rollup.EVM

theorem assign_batch_root (evm : Ethereum.State) (locals : Store) (root : Root)
    (free : locals.get? "stateRoot" = none) :
    assignStorageRef? config ⟨contract, locals⟩ evm .storage ⟨"stateRoot", []⟩
      (rootValue root) =
      .ok (⟨contract, locals⟩, Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨1⟩ ⟨root⟩) := by
  apply assignStorageRef_storage_scalar_value (er := ⟨"stateRoot", []⟩)
    (loc := bytes32Loc ⟨1⟩) free
  · simp [evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind]
  · rfl
  · rfl
  · trivial
  · exact storageLocStore_bytes32 evm ⟨1⟩ ⟨root⟩ (rootValue root) (rootValue_word root)

theorem assign_batch_number (evm : Ethereum.State) (locals : Store) (value : UInt256)
    (free : locals.get? "batchNumber" = none) :
    assignStorageRef? config ⟨contract, locals⟩ evm .storage ⟨"batchNumber", []⟩
      (.int value.toNat) =
      .ok (⟨contract, locals⟩, Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨2⟩ value) := by
  apply assignStorageRef_storage_scalar (er := ⟨"batchNumber", []⟩)
    (loc := wordLoc ⟨2⟩) free
  · simp [evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind]
  · rfl
  · rfl
  · exact storageLocStore_uint256 evm ⟨2⟩ value

end Rollup.EVM
