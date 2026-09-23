import proofs.BatchSourceHeader

open Solm ABI Ethereum Reasoning.Theory

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Rollup.EVM

/-- A valid optional owner passes its branch without changing state or locals. -/
theorem optional_owner_success (evm : Ethereum.State) (locals : Store)
    (amountName ownerName : String) (amount : Nat) (owner : Address)
    (amountArg : locals.get? amountName = some (.int amount))
    (ownerArg : locals.get? ownerName = some (.address owner))
    (valid : if amount = 0 then owner = 0 else owner ≠ 0 ∧ owner ≠ evm.executionEnv.codeOwner) :
    ExecStmt config ⟨contract, locals⟩ evm (optionalOwnerCheck amountName ownerName)
      (.ok ⟨contract, locals⟩ evm) := by
  by_cases empty : amount = 0
  · have condition : evalExpr? config ⟨contract, locals⟩ evm
        (.binary .eq (.var amountName) (.intLit 0)) = .ok (.bool true) := by
      simp only [evalExpr?, amountArg, EvalResult.ofOption, EvalResult.bind, bind,
        pure, evalBinaryOp?, empty, Nat.cast_zero, beq_self_eq_true]
    have ownerZero : owner = 0 := by simpa only [if_pos empty] using valid
    have guard : evalExpr? config ⟨contract, locals⟩ evm
        (.binary .eq (.var ownerName) (.cast (.intLit 0) (.elem .address))) = .ok (.bool true) := by
      simp only [evalExpr?, ownerArg, EvalResult.ofOption, EvalResult.bind, bind, pure,
        castValue?, evalBinaryOp?, Int.lt_irrefl, if_false, Int.toNat_zero, ownerZero]
      rfl
    exact .iteTrue condition (.consNormal (.requireTrue guard) .nil)
  · have amountNe : (Value.int (amount : Int) == Value.int 0) = false := by
      apply beq_eq_false_iff_ne.mpr
      intro same
      exact empty (by simpa using Value.int.inj same)
    have condition : evalExpr? config ⟨contract, locals⟩ evm
        (.binary .eq (.var amountName) (.intLit 0)) = .ok (.bool false) := by
      simp only [evalExpr?, amountArg, EvalResult.ofOption, EvalResult.bind, bind,
        pure, evalBinaryOp?, amountNe]
    have owners : owner ≠ 0 ∧ owner ≠ evm.executionEnv.codeOwner := by
      simpa only [if_neg empty] using valid
    have notZero : (Value.address owner == Value.address (AccountAddress.ofNat 0)) = false := by
      apply beq_eq_false_iff_ne.mpr
      simpa [AccountAddress.ofNat] using owners.1
    have notSelf : (Value.address owner == Value.address evm.executionEnv.codeOwner) = false := by
      apply beq_eq_false_iff_ne.mpr
      simpa using owners.2
    have guard : evalExpr? config ⟨contract, locals⟩ evm
        (.binary .and
          (.binary .ne (.var ownerName) (.cast (.intLit 0) (.elem .address)))
          (.binary .ne (.var ownerName) (.env .this))) = .ok (.bool true) := by
      simp only [evalExpr?, ownerArg, EvalResult.ofOption, EvalResult.bind, bind, pure,
        castValue?, envValue, evalBinaryOp?, Int.lt_irrefl, if_false, Int.toNat_zero]
      simp [notZero, notSelf]
    exact .iteFalse condition (.consNormal (.requireTrue guard) .nil)

/-- Valid batch owner checks reach the first accounting read. -/
theorem batch_owners_success (evm : Ethereum.State) (batch : Batch)
    (checks : BatchExecutionChecks evm batch) :
    ExecBlock config ⟨contract, batchHeaderLocals evm batch⟩ (batchLockedState evm)
      ((contract.transitions[1]!.body.drop 8).take 2)
      (.ok ⟨contract, batchHeaderLocals evm batch⟩ (batchLockedState evm)) := by
  have depositAmount : (batchHeaderLocals evm batch).get? "depositAmount" =
      some (.int batch.depositAmount) := by
    dsimp only [batchHeaderLocals, batchLocals]
    repeat rw [store_get_ne _ _ (by decide)]
    exact store_get_self _ _ _
  have depositOwner : (batchHeaderLocals evm batch).get? "depositOwner" =
      some (.address batch.depositOwner) := by
    dsimp only [batchHeaderLocals, batchLocals]
    repeat rw [store_get_ne _ _ (by decide)]
    exact store_get_self _ _ _
  have withdrawalAmount : (batchHeaderLocals evm batch).get? "withdrawalAmount" =
      some (.int batch.withdrawalAmount) := by
    dsimp only [batchHeaderLocals, batchLocals]
    repeat rw [store_get_ne _ _ (by decide)]
    exact store_get_self _ _ _
  have withdrawalOwner : (batchHeaderLocals evm batch).get? "withdrawalOwner" =
      some (.address batch.withdrawalOwner) := by
    dsimp only [batchHeaderLocals, batchLocals]
    repeat rw [store_get_ne _ _ (by decide)]
    exact store_get_self _ _ _
  have depositCheck := optional_owner_success (batchLockedState evm) (batchHeaderLocals evm batch)
    "depositAmount" "depositOwner" _ _ depositAmount depositOwner
    (by simpa only [batchLockedState, storageStore_executionEnv] using checks.depositOwner)
  have withdrawalCheck := optional_owner_success (batchLockedState evm) (batchHeaderLocals evm batch)
    "withdrawalAmount" "withdrawalOwner" _ _ withdrawalAmount withdrawalOwner
    (by simpa only [batchLockedState, storageStore_executionEnv] using checks.withdrawalOwner)
  exact .consNormal depositCheck (.consNormal withdrawalCheck .nil)

end Rollup.EVM
