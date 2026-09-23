import proofs.BatchSourceChecks

open Solm ABI Ethereum Reasoning.Theory

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Rollup.EVM

private abbrev Outcomes (frame : Frame) (evm : Ethereum.State) (body : List Stmt)
    (finalFrame : Frame) (finalState : Ethereum.State) : Prop :=
  ExecBlock config frame evm body .reverted ∨
    ExecBlock config frame evm body (.ok finalFrame finalState)

private theorem step_total {frame evm stmt middle before rest finalFrame finalState}
    (step : ExecStmt config frame evm stmt (.ok middle before))
    (tail : Outcomes middle before rest finalFrame finalState) :
    Outcomes frame evm (stmt :: rest) finalFrame finalState := by
  rcases tail with rejected | accepted
  · exact .inl (.consNormal step rejected)
  · exact .inr (.consNormal step accepted)

private theorem require_total {frame evm cond rest finalFrame finalState b}
    (eval : evalExpr? config frame evm cond = .ok (.bool b))
    (tail : b = true → Outcomes frame evm rest finalFrame finalState) :
    Outcomes frame evm (.require cond :: rest) finalFrame finalState := by
  cases b
  · exact .inl (.consRevert (.requireFalse eval))
  · exact step_total (.requireTrue eval) (tail rfl)

private theorem branch_total {frame evm stmt rest finalFrame finalState}
    (step : ExecStmt config frame evm stmt .reverted ∨
      ExecStmt config frame evm stmt (.ok frame evm))
    (tail : Outcomes frame evm rest finalFrame finalState) :
    Outcomes frame evm (stmt :: rest) finalFrame finalState := by
  rcases step with rejected | accepted
  · exact .inl (.consRevert rejected)
  · exact step_total accepted tail

/-- Each optional owner check either reverts or leaves state and locals unchanged. -/
theorem optional_owner_total (evm : Ethereum.State) (locals : Store)
    (amountName ownerName : String) (amount : Nat) (owner : Address)
    (amountArg : locals.get? amountName = some (.int amount))
    (ownerArg : locals.get? ownerName = some (.address owner)) :
    ExecStmt config ⟨contract, locals⟩ evm (optionalOwnerCheck amountName ownerName) .reverted ∨
    ExecStmt config ⟨contract, locals⟩ evm (optionalOwnerCheck amountName ownerName)
      (.ok ⟨contract, locals⟩ evm) := by
  have condition : evalExpr? config ⟨contract, locals⟩ evm
      (.binary .eq (.var amountName) (.intLit 0)) =
      .ok (.bool (Value.int (amount : Int) == Value.int 0)) := by
    simp only [evalExpr?, amountArg, EvalResult.ofOption, EvalResult.bind, bind,
      pure, evalBinaryOp?]
  cases branch : (Value.int (amount : Int) == Value.int 0)
  · rw [branch] at condition
    have guard : evalExpr? config ⟨contract, locals⟩ evm
        (.binary .and
          (.binary .ne (.var ownerName) (.cast (.intLit 0) (.elem .address)))
          (.binary .ne (.var ownerName) (.env .this))) =
        .ok (.bool (!(Value.address owner == Value.address (AccountAddress.ofNat 0)) &&
          !(Value.address owner == Value.address evm.executionEnv.codeOwner))) := by
      simp only [evalExpr?, ownerArg, EvalResult.ofOption, EvalResult.bind, bind, pure,
        castValue?, envValue, evalBinaryOp?, Int.lt_irrefl, if_false, Int.toNat_zero]
      cases (Value.address owner == Value.address (AccountAddress.ofNat 0)) <;> rfl
    cases passes : (!(Value.address owner == Value.address (AccountAddress.ofNat 0)) &&
        !(Value.address owner == Value.address evm.executionEnv.codeOwner))
    · rw [passes] at guard
      exact .inl (.iteFalse condition (.consRevert (.requireFalse guard)))
    · rw [passes] at guard
      exact .inr (.iteFalse condition (.consNormal (.requireTrue guard) .nil))
  · rw [branch] at condition
    have guard : evalExpr? config ⟨contract, locals⟩ evm
        (.binary .eq (.var ownerName) (.cast (.intLit 0) (.elem .address))) =
        .ok (.bool (Value.address owner == Value.address (AccountAddress.ofNat 0))) := by
      simp only [evalExpr?, ownerArg, EvalResult.ofOption, EvalResult.bind, bind, pure,
        castValue?, evalBinaryOp?, Int.lt_irrefl, if_false, Int.toNat_zero]
    cases passes : (Value.address owner == Value.address (AccountAddress.ofNat 0))
    · rw [passes] at guard
      exact .inl (.iteTrue condition (.consRevert (.requireFalse guard)))
    · rw [passes] at guard
      exact .inr (.iteTrue condition (.consNormal (.requireTrue guard) .nil))

/-- Every source batch either reverts or completes its exact storage writes. -/
theorem batch_source_total (evm : Ethereum.State) (batch : Batch) :
    ExecTransitionBody config contract evm (batchLocals batch)
      contract.transitions[1]!.body .reverted ∨
    ExecTransitionBody config contract evm (batchLocals batch)
      contract.transitions[1]!.body
      (.returned ⟨contract, batchClaimLocals evm batch⟩ (batchExecutionState evm batch) none) := by
  have block : Outcomes ⟨contract, batchLocals batch⟩ evm contract.transitions[1]!.body
      ⟨contract, batchClaimLocals evm batch⟩ (batchExecutionState evm batch) := by
    have payment : evalExpr? config ⟨contract, batchLocals batch⟩ evm
        (.binary .eq (.env .callvalue) (.intLit 0)) =
        .ok (.bool (decide (evm.executionEnv.weiValue = ⟨0⟩))) := by
      by_cases zero : evm.executionEnv.weiValue = ⟨0⟩
      · simpa only [decide_eq_true zero] using (evalCallvalueEq_true (cfg := config) (solm := ⟨contract, batchLocals batch⟩) zero)
      · simpa only [decide_eq_false zero] using (evalCallvalueEq_false (cfg := config) (solm := ⟨contract, batchLocals batch⟩) zero)
    apply require_total payment
    intro _nonpayable
    let locked := batchLockedState evm
    let next := (readWord evm evm.executionEnv.codeOwner ⟨2⟩).toNat + 1
    let locals := batchHeaderLocals evm batch
    have env : locked.executionEnv = evm.executionEnv := storageStore_executionEnv ..
    have lockEval := eval_entered evm (batchLocals batch) (by simp [batchLocals])
    have guard : evalExpr? config ⟨contract, batchLocals batch⟩ evm
        (.binary .eq (.storage ⟨"entered", []⟩) (.intLit 0)) = .ok (.bool (Value.int ((readWord evm evm.executionEnv.codeOwner ⟨6⟩).toNat : Int) == Value.int 0)) := by
      simp only [evalExpr?, lockEval, bind, EvalResult.bind, pure, evalBinaryOp?]
    apply require_total guard
    intro _unlocked
    have one : evalExpr? config ⟨contract, batchLocals batch⟩ evm (.intLit 1) = .ok (.int 1) := by
      simp only [evalExpr?, pure]
    apply step_total (.assign one
      (assign_entered evm (batchLocals batch) ⟨1⟩ (by simp [batchLocals])))
    have seqLoad := eval_batch_sequencer locked (batchLocals batch) (by simp [batchLocals])
    have sameSeq : getterValue locked .sequencer = getterValue evm .sequencer := by
      have sameWord : readWord locked evm.executionEnv.codeOwner ⟨0⟩ =
          readWord evm evm.executionEnv.codeOwner ⟨0⟩ :=
        storageLoad_storageStore_ne evm _ (by decide)
      simp only [getterValue, env, sameWord]
    have authorization : evalExpr? config ⟨contract, batchLocals batch⟩ locked
        (.binary .eq (.env .caller) (.storage ⟨"sequencer", []⟩)) = .ok (.bool (Value.address evm.executionEnv.source == getterValue evm .sequencer)) := by
      simp only [evalExpr?, seqLoad, EvalResult.bind, bind, pure, envValue, env, sameSeq]
      simp only [getterValue, evalBinaryOp?]
    apply require_total authorization
    intro _authorized
    have sameNumber : readWord locked evm.executionEnv.codeOwner ⟨2⟩ =
        readWord evm evm.executionEnv.codeOwner ⟨2⟩ :=
      storageLoad_storageStore_ne evm _ (by decide)
    have numberLoad := eval_batch_number locked (batchLocals batch) (by simp [batchLocals])
    have nextEval : evalExpr? config ⟨contract, batchLocals batch⟩ locked
        (.binary .add (.storage ⟨"batchNumber", []⟩) (.intLit 1)) = .ok (.int next) := by
      simp only [evalExpr?, numberLoad, EvalResult.bind, bind, pure, evalBinaryOp?,
        env, sameNumber, next, Nat.cast_add, Nat.cast_one]
    apply step_total (.letDecl nextEval)
    have nextArg : locals.get? "nextNumber" = some (.int next) := store_get_self _ _ _
    have numberArg : locals.get? "nextBatchNumber" = some (.int batch.number) := by
      dsimp only [locals, batchHeaderLocals, batchLocals]
      repeat rw [store_get_ne _ _ (by decide)]
      exact store_get_self _ _ _
    have oldRootArg : locals.get? "oldRoot" = some (rootValue batch.oldRoot) := by
      dsimp only [locals, batchHeaderLocals, batchLocals]
      repeat rw [store_get_ne _ _ (by decide)]
      exact store_get_self _ _ _
    have range : evalExpr? config ⟨contract, locals⟩ locked
        (.binary .lt (.var "nextNumber") (.intLit (2 ^ 256))) = .ok (.bool (decide ((next : Int) < 2 ^ 256))) := by
      simp only [evalExpr?, nextArg, EvalResult.ofOption, EvalResult.bind,
        bind, pure, evalBinaryOp?]
    apply require_total range
    intro inRange
    have numberFits : next < wordLimit := by
      exact_mod_cast (of_decide_eq_true inRange)
    have number : evalExpr? config ⟨contract, locals⟩ locked
        (.binary .eq (.var "nextBatchNumber") (.var "nextNumber")) = .ok (.bool (Value.int (batch.number : Int) == Value.int (next : Int))) := by
      simp only [evalExpr?, numberArg, nextArg, EvalResult.ofOption,
        EvalResult.bind, bind, evalBinaryOp?]
    apply require_total number
    intro sameNumberArg
    have nextNumber : batch.number = next := by simpa using sameNumberArg
    have numberBound : batch.number < wordLimit := nextNumber.symm ▸ numberFits
    have rootLoad := eval_batch_root locked locals (by simp [locals, batchHeaderLocals, batchLocals])
    have sameRoot : readWord locked evm.executionEnv.codeOwner ⟨1⟩ =
        readWord evm evm.executionEnv.codeOwner ⟨1⟩ :=
      storageLoad_storageStore_ne evm _ (by decide)
    have root : evalExpr? config ⟨contract, locals⟩ locked
        (.binary .eq (.var "oldRoot") (.storage ⟨"stateRoot", []⟩)) = .ok (.bool (rootValue batch.oldRoot == rootValue (readWord evm evm.executionEnv.codeOwner ⟨1⟩).val)) := by
      simp only [evalExpr?, oldRootArg, rootLoad, EvalResult.ofOption, EvalResult.bind,
        bind, env, sameRoot]
      simp only [rootValue, evalBinaryOp?]
    apply require_total root
    intro _rootMatches
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
    apply branch_total (optional_owner_total (batchLockedState evm) (batchHeaderLocals evm batch)
      "depositAmount" "depositOwner" _ _ depositAmount depositOwner)
    apply branch_total (optional_owner_total (batchLockedState evm) (batchHeaderLocals evm batch)
      "withdrawalAmount" "withdrawalOwner" _ _ withdrawalAmount withdrawalOwner)
    have ownerArg : (batchHeaderLocals evm batch).get? "depositOwner" =
        some (.address batch.depositOwner) := by
      dsimp only [batchHeaderLocals, batchLocals]
      repeat rw [store_get_ne _ _ (by decide)]
      exact store_get_self _ _ _
    have env : (batchLockedState evm).executionEnv = evm.executionEnv := storageStore_executionEnv ..
    have load := eval_batch_pending (batchLockedState evm) (batchHeaderLocals evm batch)
      batch.depositOwner (by simp [batchHeaderLocals, batchLocals]) ownerArg
    rw [env] at load
    change evalExpr? config ⟨contract, batchHeaderLocals evm batch⟩ (batchLockedState evm)
      (.storage ⟨"pendingDeposits", [.mindex (.var "depositOwner")]⟩) =
      .ok (.int (batchDepositCredit evm batch)) at load
    apply step_total (.letDecl load)
    have amountArg : (batchDepositLocals evm batch).get? "depositAmount" =
        some (.int batch.depositAmount) := by
      dsimp only [batchDepositLocals, batchHeaderLocals, batchLocals]
      repeat rw [store_get_ne _ _ (by decide)]
      exact store_get_self _ _ _
    have creditArg : (batchDepositLocals evm batch).get? "depositCredit" =
        some (.int (batchDepositCredit evm batch)) := store_get_self _ _ _
    have guard : evalExpr? config ⟨contract, batchDepositLocals evm batch⟩ (batchLockedState evm)
        (.binary .le (.var "depositAmount") (.var "depositCredit")) = .ok (.bool (decide ((batch.depositAmount : Int) ≤ batchDepositCredit evm batch))) := by
      simp only [evalExpr?, amountArg, creditArg, EvalResult.ofOption, EvalResult.bind,
        bind, evalBinaryOp?]
    apply require_total guard
    intro allowed
    have depositCovered : batch.depositAmount ≤ batchDepositCredit evm batch := by
      exact_mod_cast (of_decide_eq_true allowed)
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
    rw [remainingWord, env] at assign
    have subtract : evalExpr? config ⟨contract, batchDepositLocals evm batch⟩ (batchLockedState evm)
        (.binary .sub (.var "depositCredit") (.var "depositAmount")) =
        .ok (.int (Int.ofNat (batchDepositCredit evm batch - batch.depositAmount))) := by
      simp only [evalExpr?, creditArg, amountArg, EvalResult.ofOption, EvalResult.bind,
        bind, evalBinaryOp?]
      exact congrArg (fun value => EvalResult.ok (Value.int value)) (Int.ofNat_sub depositCovered).symm
    apply step_total (.assign subtract assign)
    have env : (batchDebitedState evm batch).executionEnv = evm.executionEnv := by
      simp only [batchDebitedState, batchLockedState, storageStore_executionEnv]
    have depositArg : (batchDepositLocals evm batch).get? "depositAmount" =
        some (.int batch.depositAmount) := by
      dsimp only [batchDepositLocals, batchHeaderLocals, batchLocals]
      repeat rw [store_get_ne _ _ (by decide)]
      exact store_get_self _ _ _
    have load := eval_batch_backing (batchDebitedState evm batch) (batchDepositLocals evm batch)
      (by simp [batchDepositLocals, batchHeaderLocals, batchLocals])
    have add : evalExpr? config ⟨contract, batchDepositLocals evm batch⟩ (batchDebitedState evm batch)
        (.binary .add (.storage ⟨"backing", []⟩) (.var "depositAmount")) =
        .ok (.int (batchAvailable evm batch)) := by
      simp only [evalExpr?, load, depositArg, EvalResult.ofOption, EvalResult.bind,
        bind, evalBinaryOp?, env, batchAvailable, Nat.cast_add]
    apply step_total (.letDecl add)
    have availableArg : (batchBackingLocals evm batch).get? "available" =
        some (.int (batchAvailable evm batch)) := store_get_self _ _ _
    have withdrawalArg : (batchBackingLocals evm batch).get? "withdrawalAmount" =
        some (.int batch.withdrawalAmount) := by
      dsimp only [batchBackingLocals, batchDepositLocals, batchHeaderLocals, batchLocals]
      repeat rw [store_get_ne _ _ (by decide)]
      exact store_get_self _ _ _
    have range : evalExpr? config ⟨contract, batchBackingLocals evm batch⟩ (batchDebitedState evm batch)
        (.binary .lt (.var "available") (.intLit (2 ^ 256))) = .ok (.bool (decide ((batchAvailable evm batch : Int) < 2 ^ 256))) := by
      simp only [evalExpr?, availableArg, EvalResult.ofOption, EvalResult.bind, bind, pure,
        evalBinaryOp?]
    apply require_total range
    intro inRange
    have backingFits : batchAvailable evm batch < wordLimit := by
      exact_mod_cast (of_decide_eq_true inRange)
    have guard : evalExpr? config ⟨contract, batchBackingLocals evm batch⟩ (batchDebitedState evm batch)
        (.binary .le (.var "withdrawalAmount") (.var "available")) = .ok (.bool (decide ((batch.withdrawalAmount : Int) ≤ batchAvailable evm batch))) := by
      simp only [evalExpr?, withdrawalArg, availableArg, EvalResult.ofOption,
        EvalResult.bind, bind, evalBinaryOp?]
    apply require_total guard
    intro allowed
    have withdrawalCovered : batch.withdrawalAmount ≤ batchAvailable evm batch := by
      exact_mod_cast (of_decide_eq_true allowed)
    have remainderBound : batchAvailable evm batch - batch.withdrawalAmount < wordLimit :=
      lt_of_le_of_lt (Nat.sub_le _ _) backingFits
    have remainderWord : (UInt256.ofNat (batchAvailable evm batch - batch.withdrawalAmount)).toNat =
        batchAvailable evm batch - batch.withdrawalAmount := ulit_toNat' _ remainderBound
    have assign := assign_batch_backing (batchDebitedState evm batch) (batchBackingLocals evm batch)
      (UInt256.ofNat (batchAvailable evm batch - batch.withdrawalAmount))
      (by simp [batchBackingLocals, batchDepositLocals, batchHeaderLocals, batchLocals])
    rw [remainderWord, env] at assign
    have subtract : evalExpr? config ⟨contract, batchBackingLocals evm batch⟩ (batchDebitedState evm batch)
        (.binary .sub (.var "available") (.var "withdrawalAmount")) =
        .ok (.int (Int.ofNat (batchAvailable evm batch - batch.withdrawalAmount))) := by
      simp only [evalExpr?, availableArg, withdrawalArg, EvalResult.ofOption,
        EvalResult.bind, bind, evalBinaryOp?]
      exact congrArg (fun value => EvalResult.ok (Value.int value)) (Int.ofNat_sub withdrawalCovered).symm
    apply step_total (.assign subtract assign)
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
    apply step_total (.letDecl add)
    have creditArg : (batchClaimLocals evm batch).get? "nextCredit" =
        some (.int (batchNextCredit evm batch)) := store_get_self _ _ _
    have range : evalExpr? config ⟨contract, batchClaimLocals evm batch⟩ (batchBackedState evm batch)
        (.binary .lt (.var "nextCredit") (.intLit (2 ^ 256))) = .ok (.bool (decide ((batchNextCredit evm batch : Int) < 2 ^ 256))) := by
      simp only [evalExpr?, creditArg, EvalResult.ofOption, EvalResult.bind, bind, pure,
        evalBinaryOp?]
    apply require_total range
    intro inRange
    have claimFits : batchNextCredit evm batch < wordLimit := by
      exact_mod_cast (of_decide_eq_true inRange)
    have ownerArg' : (batchClaimLocals evm batch).get? "withdrawalOwner" =
        some (.address batch.withdrawalOwner) := by
      rw [batchClaimLocals, store_get_ne _ _ (by decide)]
      exact ownerArg
    have assign := assign_batch_claims (batchBackedState evm batch) (batchClaimLocals evm batch)
      batch.withdrawalOwner (UInt256.ofNat (batchNextCredit evm batch))
      (by simp [batchClaimLocals, batchBackingLocals, batchDepositLocals, batchHeaderLocals, batchLocals]) ownerArg'
    rw [ulit_toNat' _ claimFits, env] at assign
    have eval : evalExpr? config ⟨contract, batchClaimLocals evm batch⟩ (batchBackedState evm batch)
        (.var "nextCredit") = .ok (.int (batchNextCredit evm batch)) := by
      simp only [evalExpr?, creditArg, EvalResult.ofOption]
    apply step_total (.assign eval assign)
    have creditedEnv : (batchCreditedState evm batch).executionEnv = evm.executionEnv := by
      simp only [batchCreditedState, batchBackedState, batchDebitedState,
        batchLockedState, storageStore_executionEnv]
    have rootedEnv : (batchRootedState evm batch).executionEnv = evm.executionEnv := by
      simp only [batchRootedState, storageStore_executionEnv, creditedEnv]
    have numberedEnv : (batchNumberedState evm batch).executionEnv = evm.executionEnv := by
      simp only [batchNumberedState, storageStore_executionEnv, rootedEnv]
    have rootArg : (batchClaimLocals evm batch).get? "newRoot" = some (rootValue batch.newRoot) := by
      dsimp only [batchClaimLocals, batchBackingLocals, batchDepositLocals, batchHeaderLocals, batchLocals]
      repeat rw [store_get_ne _ _ (by decide)]
      exact store_get_self _ _ _
    have numberArg : (batchClaimLocals evm batch).get? "nextBatchNumber" = some (.int batch.number) := by
      dsimp only [batchClaimLocals, batchBackingLocals, batchDepositLocals, batchHeaderLocals, batchLocals]
      repeat rw [store_get_ne _ _ (by decide)]
      exact store_get_self _ _ _
    have rootEval : evalExpr? config ⟨contract, batchClaimLocals evm batch⟩ (batchCreditedState evm batch)
        (.var "newRoot") = .ok (rootValue batch.newRoot) := by
      simp only [evalExpr?, rootArg, EvalResult.ofOption]
    have rootAssign := assign_batch_root (batchCreditedState evm batch) (batchClaimLocals evm batch)
      batch.newRoot (by simp [batchClaimLocals, batchBackingLocals, batchDepositLocals,
        batchHeaderLocals, batchLocals])
    rw [creditedEnv] at rootAssign
    have numberEval : evalExpr? config ⟨contract, batchClaimLocals evm batch⟩ (batchRootedState evm batch)
        (.var "nextBatchNumber") = .ok (.int batch.number) := by
      simp only [evalExpr?, numberArg, EvalResult.ofOption]
    have numberAssign := assign_batch_number (batchRootedState evm batch) (batchClaimLocals evm batch)
      (UInt256.ofNat batch.number) (by simp [batchClaimLocals, batchBackingLocals, batchDepositLocals,
        batchHeaderLocals, batchLocals])
    rw [ulit_toNat' _ numberBound, rootedEnv] at numberAssign
    have unlock := assign_entered (batchNumberedState evm batch) (batchClaimLocals evm batch) ⟨0⟩
      (by simp [batchClaimLocals, batchBackingLocals, batchDepositLocals, batchHeaderLocals, batchLocals])
    rw [numberedEnv] at unlock
    exact .inr (.consNormal (.assign rootEval rootAssign) (.consNormal (.assign numberEval numberAssign)
      (.consNormal (.assign (by simp only [evalExpr?, pure]; rfl) unlock) .nil)))
  rcases block with rejected | accepted
  · exact .inl (.execBlockRevert rejected)
  · exact .inr (.execBlockOK accepted)

/-- A failed source check has an actual revert execution. -/
theorem batch_source_rejected (evm : Ethereum.State) (batch : Batch)
    (failed : ¬ BatchExecutionChecks evm batch) :
    ExecTransitionBody config contract evm (batchLocals batch)
      contract.transitions[1]!.body .reverted := by
  rcases batch_source_total evm batch with rejected | accepted
  · exact rejected
  · exact (failed (batch_source_checks evm _ batch _ _ accepted)).elim

end Rollup.EVM
