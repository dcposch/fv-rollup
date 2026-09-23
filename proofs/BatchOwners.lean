import proofs.SourceBranches
import proofs.BatchContinuity
import semantics.Semantics
import semantics.Model
import Reasoning.SolmBody

open Solm ABI Ethereum Reasoning.Theory

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Rollup.EVM

def optionalOwnerCheck (amountName ownerName : String) : Stmt :=
  .ite (.binary .eq (.var amountName) (.intLit 0))
    [.require (.binary .eq (.var ownerName) (.cast (.intLit 0) (.elem .address)))]
    [.require (.binary .and
      (.binary .ne (.var ownerName) (.cast (.intLit 0) (.elem .address)))
      (.binary .ne (.var ownerName) (.env .this)))]

/-- The owner check accepts zero effects only with the zero address. -/
theorem accepted_optional_owner (evm : Ethereum.State) (locals : Store)
    (amountName ownerName : String) (amount : Nat) (owner : Address)
    (amountArg : locals.get? amountName = some (.int amount))
    (ownerArg : locals.get? ownerName = some (.address owner))
    {rest frame out values}
    (run : ExecFuncBody config ⟨contract, locals⟩ evm
      (optionalOwnerCheck amountName ownerName :: rest) (.returned frame out values)) :
    (if amount = 0 then owner = 0 else owner ≠ 0 ∧ owner ≠ evm.executionEnv.codeOwner) ∧
    ExecFuncBody config ⟨contract, locals⟩ evm rest (.returned frame out values) := by
  obtain ⟨branch, remaining⟩ := accepted_require_branch run
  refine ⟨?_, remaining⟩
  rcases branch with ⟨zero, check⟩ | ⟨nonzero, check⟩
  · have isZero : amount = 0 := by
      simp only [evalExpr?, amountArg, EvalResult.ofOption, EvalResult.bind, bind, pure,
        evalBinaryOp?] at zero
      simpa using zero
    rw [if_pos isZero]
    simp only [evalExpr?, ownerArg, EvalResult.ofOption, EvalResult.bind, bind, pure,
      castValue?, evalBinaryOp?, Int.lt_irrefl, if_false, Int.toNat_zero] at check
    simpa [AccountAddress.ofNat] using check
  · have isNonzero : amount ≠ 0 := by
      simp only [evalExpr?, amountArg, EvalResult.ofOption, EvalResult.bind, bind, pure,
        evalBinaryOp?] at nonzero
      simpa using nonzero
    rw [if_neg isNonzero]
    simp only [evalExpr?, ownerArg, EvalResult.ofOption, EvalResult.bind, bind, pure,
      castValue?, envValue, evalBinaryOp?, Int.lt_irrefl, if_false, Int.toNat_zero] at check
    by_cases ownerZero : owner = 0
    · subst owner
      cases check
    · have notZero : (Value.address owner == Value.address (AccountAddress.ofNat 0)) = false := by
        apply beq_eq_false_iff_ne.mpr
        simpa [AccountAddress.ofNat] using ownerZero
      simp only [notZero, Bool.not_false] at check
      exact ⟨ownerZero, by simpa using check⟩

/-- Both batch owner checks pass before accounting writes start. -/
theorem batch_source_after_owners (evm out : Ethereum.State) (batch : Batch)
    (frame : Frame) (values : Option (List Value)) (keys : AccessScope)
    (run : ExecTransitionBody config contract evm (batchLocals batch)
      contract.transitions[1]!.body (.returned frame out values)) :
    optionalOwner (project evm evm.executionEnv.codeOwner keys) batch.depositOwner batch.depositAmount ∧
    optionalOwner (project evm evm.executionEnv.codeOwner keys) batch.withdrawalOwner batch.withdrawalAmount ∧
    ExecFuncBody config ⟨contract, batchHeaderLocals evm batch⟩ (batchLockedState evm)
      (contract.transitions[1]!.body.drop 10) (.returned frame out values) := by
  have header := (batch_source_header evm out batch frame values run).2.2.2
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
  obtain ⟨depositCheck, afterDeposit⟩ := accepted_optional_owner _ _
    "depositAmount" "depositOwner" _ _ depositAmount depositOwner header
  obtain ⟨withdrawalCheck, remaining⟩ := accepted_optional_owner _ _
    "withdrawalAmount" "withdrawalOwner" _ _ withdrawalAmount withdrawalOwner afterDeposit
  refine ⟨?_, ?_, remaining⟩
  · simpa only [optionalOwner, validOwner, project, batchLockedState,
      storageStore_executionEnv] using depositCheck
  · simpa only [optionalOwner, validOwner, project, batchLockedState,
      storageStore_executionEnv] using withdrawalCheck

end Rollup.EVM
