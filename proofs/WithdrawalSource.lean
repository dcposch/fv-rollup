import semantics.WithdrawalState
import proofs.Payments
import proofs.SourceStorage

open Solm ABI Ethereum Reasoning.Theory

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Rollup.EVM

def withdrawalLocals (owner : Address) (amount : Nat) : Store :=
  (((∅ : Store).insert "owner" (.address owner)).insert "amount" (.int amount))

def withdrawalCredit (evm : Ethereum.State) (owner : Address) : Nat :=
  (readWord (withdrawalLockedState evm) evm.executionEnv.codeOwner (keySlot (.claims owner))).toNat

def withdrawalCreditLocals (evm : Ethereum.State) (owner : Address) (amount : Nat) : Store :=
  (withdrawalLocals owner amount).insert "credit" (.int (withdrawalCredit evm owner))

/-- Read credit after the lock write, as the contract does. -/
structure WithdrawalExecutionChecks (evm : Ethereum.State) (owner : Address) (amount : Nat) : Prop where
  nonpayable : evm.executionEnv.weiValue = ⟨0⟩
  unlocked : readWord evm evm.executionEnv.codeOwner ⟨6⟩ = ⟨0⟩
  positive : amount ≠ 0
  covered : amount ≤ withdrawalCredit evm owner

private theorem owner_arg (owner : Address) (amount : Nat) :
    (withdrawalLocals owner amount).get? "owner" = some (.address owner) := by
  rw [withdrawalLocals, store_get_ne _ _ (by decide), store_get_self]

private theorem lock_eval (evm : Ethereum.State) (owner : Address) (amount : Nat) :
    evalExpr? config ⟨contract, withdrawalLocals owner amount⟩ evm lockGuard =
      .ok (.bool (decide (readWord evm evm.executionEnv.codeOwner ⟨6⟩ = ⟨0⟩))) := by
  have load := eval_entered evm (withdrawalLocals owner amount) (by simp [withdrawalLocals])
  simp only [lockGuard, evalExpr?, load, bind, EvalResult.bind, pure, evalBinaryOp?]
  congr 2
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, Value.int.injEq, decide_eq_true_eq]
  constructor
  · intro zero
    exact uint256_toNat_eq_zero (Int.ofNat.inj zero)
  · intro zero
    rw [zero]
    rfl

private theorem amount_eval (evm : Ethereum.State) (owner : Address) (amount : Nat) :
    evalExpr? config ⟨contract, withdrawalLocals owner amount⟩ evm
      (.binary .ne (.var "amount") (.intLit 0)) = .ok (.bool (decide (amount ≠ 0))) := by
  have arg : (withdrawalLocals owner amount).get? "amount" = some (.int amount) := store_get_self _ _ _
  simp only [evalExpr?, arg, EvalResult.ofOption, EvalResult.bind, bind, pure, evalBinaryOp?]
  congr 2
  apply Bool.eq_iff_iff.mpr
  simp

private theorem claims_reference (evm : Ethereum.State) (locals : Store) (owner : Address)
    (arg : locals.get? "owner" = some (.address owner)) :
    evalStorageRef config ⟨contract, locals⟩ evm
      ⟨"pendingWithdrawals", [.mindex (.var "owner")]⟩ =
      .ok ⟨"pendingWithdrawals", [.mindex (.address owner)]⟩ := by
  simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, evalExpr?, arg,
    EvalResult.ofOption, EvalResult.bind, pure, bind, valueToKey?]

private theorem credit_eval (evm : Ethereum.State) (owner : Address) (amount : Nat) :
    evalExpr? config ⟨contract, withdrawalLocals owner amount⟩ (withdrawalLockedState evm)
      (.storage ⟨"pendingWithdrawals", [.mindex (.var "owner")]⟩) =
      .ok (.int (withdrawalCredit evm owner)) := by
  apply evalExpr_storage_scalar_value (er := ⟨"pendingWithdrawals", [.mindex (.address owner)]⟩)
    (t := .int uint256) (loc := wordLoc (keySlot (.claims owner)))
    (by simp [withdrawalLocals])
  · exact claims_reference _ _ owner (owner_arg owner amount)
  · rfl
  · rfl
  · simpa only [withdrawalCredit, withdrawalLockedState, storageStore_executionEnv] using
      storageLocLoad_uint256 (withdrawalLockedState evm) (keySlot (.claims owner))

private theorem covered_eval (evm : Ethereum.State) (owner : Address) (amount : Nat) :
    evalExpr? config ⟨contract, withdrawalCreditLocals evm owner amount⟩ (withdrawalLockedState evm)
      (.binary .le (.var "amount") (.var "credit")) =
      .ok (.bool (decide (amount ≤ withdrawalCredit evm owner))) := by
  have creditArg : (withdrawalCreditLocals evm owner amount).get? "credit" =
      some (.int (withdrawalCredit evm owner)) := store_get_self _ _ _
  have amountArg : (withdrawalCreditLocals evm owner amount).get? "amount" = some (.int amount) := by
    rw [withdrawalCreditLocals, store_get_ne _ _ (by decide), withdrawalLocals, store_get_self]
  simp only [evalExpr?, amountArg, creditArg, EvalResult.ofOption, EvalResult.bind, bind,
    evalBinaryOp?, Int.ofNat_le]

/-- Passing checks reach the payment with the lock set and the credit saved. -/
theorem withdrawal_prelude_exact (evm : Ethereum.State) (owner : Address) (amount : Nat)
    (checks : WithdrawalExecutionChecks evm owner amount) :
    ExactBlock config ⟨contract, withdrawalLocals owner amount⟩ evm withdrawalPrelude
      (.ok ⟨contract, withdrawalCreditLocals evm owner amount⟩ (withdrawalLockedState evm)) := by
  refine exact_cons (exact_require_true (evalCallvalueEq_true checks.nonpayable)) ?_
  refine exact_cons (exact_require_true (by simpa [checks.unlocked] using lock_eval evm owner amount)) ?_
  refine exact_cons (exact_assign (value := .int 1) ?_
    (assign_entered evm (withdrawalLocals owner amount) ⟨1⟩ (by simp [withdrawalLocals]))) ?_
  · simp only [evalExpr?, pure]
  refine exact_cons (exact_require_true (by
    simpa [checks.positive] using amount_eval (withdrawalLockedState evm) owner amount)) ?_
  refine exact_cons (exact_let (credit_eval evm owner amount)) ?_
  exact exact_cons (exact_require_true (by simpa [checks.covered] using covered_eval evm owner amount))
    (exact_nil ..)

/-- Every accepted prelude passed the four withdrawal checks. -/
theorem withdrawal_prelude_checks (evm out : Ethereum.State) (owner : Address) (amount : Nat)
    (frame : Frame)
    (run : ExecBlock config ⟨contract, withdrawalLocals owner amount⟩ evm withdrawalPrelude
      (.ok frame out)) : WithdrawalExecutionChecks evm owner amount := by
  have body := ExecFuncBody.execBlockOK run
  obtain ⟨paymentGuard, afterPayment⟩ := accepted_require body
  have nonpayable : evm.executionEnv.weiValue = ⟨0⟩ := by
    by_contra nonzero
    rw [evalCallvalueEq_false nonzero] at paymentGuard
    cases paymentGuard
  obtain ⟨lockTest, afterLockTest⟩ := accepted_require afterPayment
  have unlocked : readWord evm evm.executionEnv.codeOwner ⟨6⟩ = ⟨0⟩ := by
    change evalExpr? config ⟨contract, withdrawalLocals owner amount⟩ evm lockGuard =
      .ok (.bool true) at lockTest
    rw [lock_eval] at lockTest
    simpa using lockTest
  have afterLock := accepted_assign (value := .int 1) (by simp only [evalExpr?, pure])
    (assign_entered evm (withdrawalLocals owner amount) ⟨1⟩ (by simp [withdrawalLocals])) afterLockTest
  obtain ⟨amountTest, afterAmount⟩ := accepted_require afterLock
  have positive : amount ≠ 0 := by
    rw [amount_eval] at amountTest
    simpa using amountTest
  have afterCredit := accepted_exact (exact_let (credit_eval evm owner amount)) afterAmount
  have coveredTest := (accepted_require afterCredit).1
  have covered : amount ≤ withdrawalCredit evm owner := by
    change evalExpr? config ⟨contract, withdrawalCreditLocals evm owner amount⟩ (withdrawalLockedState evm)
      (.binary .le (.var "amount") (.var "credit")) = .ok (.bool true) at coveredTest
    rw [covered_eval] at coveredTest
    simpa using coveredTest
  exact ⟨nonpayable, unlocked, positive, covered⟩

/-- A successful prelude has the exact local frame and locked state. -/
theorem withdrawal_prelude_result (evm out : Ethereum.State) (owner : Address) (amount : Nat)
    (frame : Frame)
    (run : ExecBlock config ⟨contract, withdrawalLocals owner amount⟩ evm withdrawalPrelude
      (.ok frame out)) :
    WithdrawalExecutionChecks evm owner amount ∧
      frame = ⟨contract, withdrawalCreditLocals evm owner amount⟩ ∧ out = withdrawalLockedState evm := by
  have checks := withdrawal_prelude_checks evm out owner amount frame run
  have same := (withdrawal_prelude_exact evm owner amount checks).unique _ run
  exact ⟨checks, ExecResult.ok.inj same⟩

/-- A failed prelude check reverts before any external payment. -/
theorem withdrawal_prelude_rejected (evm : Ethereum.State) (owner : Address) (amount : Nat)
    (failed : ¬ WithdrawalExecutionChecks evm owner amount) :
    ExactBlock config ⟨contract, withdrawalLocals owner amount⟩ evm withdrawalPrelude .reverted := by
  by_cases nonpayable : evm.executionEnv.weiValue = ⟨0⟩
  · refine exact_cons (exact_require_true (evalCallvalueEq_true nonpayable)) ?_
    by_cases unlocked : readWord evm evm.executionEnv.codeOwner ⟨6⟩ = ⟨0⟩
    · refine exact_cons (exact_require_true (by simpa [unlocked] using lock_eval evm owner amount)) ?_
      refine exact_cons (exact_assign (value := .int 1) ?_
        (assign_entered evm (withdrawalLocals owner amount) ⟨1⟩ (by simp [withdrawalLocals]))) ?_
      · simp only [evalExpr?, pure]
      by_cases positive : amount ≠ 0
      · refine exact_cons (exact_require_true (by
          simpa [positive] using amount_eval (withdrawalLockedState evm) owner amount)) ?_
        refine exact_cons (exact_let (credit_eval evm owner amount)) ?_
        have uncovered : ¬ amount ≤ withdrawalCredit evm owner :=
          fun covered => failed ⟨nonpayable, unlocked, positive, covered⟩
        apply exact_require_false
        simpa [uncovered] using covered_eval evm owner amount
      · apply exact_require_false
        simpa [positive] using amount_eval (withdrawalLockedState evm) owner amount
    · apply exact_require_false
      simpa [unlocked] using lock_eval evm owner amount
  · exact exact_require_false (evalCallvalueEq_false nonpayable)

def withdrawalReturnLocals (evm : Ethereum.State) (owner : Address) (amount : Nat)
    (paid : Bool) (data : ByteArray) : Store :=
  ((withdrawalCreditLocals evm owner amount).insert "success" (.bool paid)).insert "_data" (.bytes data)

def withdrawalDebitedState (before after : Ethereum.State) (owner : Address) (amount : Nat) : Ethereum.State :=
  Solm.EVM.storageStore after after.executionEnv.codeOwner (keySlot (.claims owner))
    (UInt256.ofNat (withdrawalCredit before owner - amount))

def withdrawalFinalState (before after : Ethereum.State) (owner : Address) (amount : Nat) : Ethereum.State :=
  Solm.EVM.storageStore (withdrawalDebitedState before after owner amount) after.executionEnv.codeOwner ⟨6⟩ ⟨0⟩

private theorem paid_eval (before after : Ethereum.State) (owner : Address) (amount : Nat)
    (paid : Bool) (data : ByteArray) :
    evalExpr? config ⟨contract, withdrawalReturnLocals before owner amount paid data⟩ after
      (.var "success") = .ok (.bool paid) := by
  have arg : (withdrawalReturnLocals before owner amount paid data).get? "success" = some (.bool paid) := by
    rw [withdrawalReturnLocals, store_get_ne _ _ (by decide), store_get_self]
  simp only [evalExpr?, arg, EvalResult.ofOption]

private theorem assign_claim (evm : Ethereum.State) (locals : Store) (owner : Address) (value : UInt256)
    (free : locals.get? "pendingWithdrawals" = none)
    (arg : locals.get? "owner" = some (.address owner)) :
    assignStorageRef? config ⟨contract, locals⟩ evm .storage
      ⟨"pendingWithdrawals", [.mindex (.var "owner")]⟩ (.int value.toNat) =
      .ok (⟨contract, locals⟩, Solm.EVM.storageStore evm evm.executionEnv.codeOwner (keySlot (.claims owner)) value) := by
  apply assignStorageRef_storage_scalar (er := ⟨"pendingWithdrawals", [.mindex (.address owner)]⟩)
    (loc := wordLoc (keySlot (.claims owner))) free
  · exact claims_reference evm locals owner arg
  · rfl
  · rfl
  · exact storageLocStore_uint256 evm _ value

/-- A successful payment debits the saved credit, then releases the lock. -/
theorem withdrawal_postlude_exact (before after : Ethereum.State) (owner : Address) (amount : Nat)
    (data : ByteArray) (covered : amount ≤ withdrawalCredit before owner) :
    ExactBlock config ⟨contract, withdrawalReturnLocals before owner amount true data⟩ after
      withdrawalPostlude
      (.ok ⟨contract, withdrawalReturnLocals before owner amount true data⟩
        (withdrawalFinalState before after owner amount)) := by
  refine exact_cons (exact_require_true (paid_eval before after owner amount true data)) ?_
  let locals := withdrawalReturnLocals before owner amount true data
  have ownerArg : locals.get? "owner" = some (.address owner) := by
    dsimp only [locals, withdrawalReturnLocals, withdrawalCreditLocals, withdrawalLocals]
    repeat rw [store_get_ne _ _ (by decide)]
    exact store_get_self _ _ _
  have amountArg : locals.get? "amount" = some (.int amount) := by
    dsimp only [locals, withdrawalReturnLocals, withdrawalCreditLocals, withdrawalLocals]
    repeat rw [store_get_ne _ _ (by decide)]
    exact store_get_self _ _ _
  have creditArg : locals.get? "credit" = some (.int (withdrawalCredit before owner)) := by
    dsimp only [locals, withdrawalReturnLocals, withdrawalCreditLocals]
    repeat rw [store_get_ne _ _ (by decide)]
    exact store_get_self _ _ _
  have subtract : evalExpr? config ⟨contract, locals⟩ after
      (.binary .sub (.var "credit") (.var "amount")) =
      .ok (.int (withdrawalCredit before owner - amount : Nat)) := by
    simp only [evalExpr?, creditArg, amountArg, EvalResult.ofOption, EvalResult.bind, bind, evalBinaryOp?]
    exact congrArg (fun value => EvalResult.ok (Value.int value)) (Int.ofNat_sub covered).symm
  have remainderBound : withdrawalCredit before owner - amount < wordLimit :=
    lt_of_le_of_lt (Nat.sub_le _ _) (readWord (withdrawalLockedState before)
      before.executionEnv.codeOwner (keySlot (.claims owner))).val.isLt
  have assign := assign_claim after locals owner
    (UInt256.ofNat (withdrawalCredit before owner - amount))
    (by simp [locals, withdrawalReturnLocals, withdrawalCreditLocals, withdrawalLocals]) ownerArg
  rw [ulit_toNat' _ remainderBound] at assign
  refine exact_cons (exact_assign subtract assign) ?_
  have unlock := assign_entered (withdrawalDebitedState before after owner amount) locals ⟨0⟩
    (by simp [locals, withdrawalReturnLocals, withdrawalCreditLocals, withdrawalLocals])
  simp only [withdrawalDebitedState, storageStore_executionEnv] at unlock
  exact exact_cons (exact_assign (by simp only [evalExpr?, pure]; rfl) unlock) (exact_nil ..)

/-- A failed payment reverts before the credit debit. -/
theorem withdrawal_postlude_rejected (before after : Ethereum.State) (owner : Address) (amount : Nat)
    (data : ByteArray) :
    ExactBlock config ⟨contract, withdrawalReturnLocals before owner amount false data⟩ after
      withdrawalPostlude .reverted :=
  exact_require_false (paid_eval before after owner amount false data)

end Rollup.EVM
