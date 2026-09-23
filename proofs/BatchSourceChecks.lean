import proofs.BatchSourceSuccess

open Solm ABI Ethereum Reasoning.Theory

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Rollup.EVM

/-- Every accepted source batch satisfies the execution checks. -/
theorem batch_source_checks (evm out : Ethereum.State) (batch : Batch)
    (frame : Frame) (values : Option (List Value))
    (run : ExecTransitionBody config contract evm (batchLocals batch)
      contract.transitions[1]!.body (.returned frame out values)) :
    BatchExecutionChecks evm batch := by
  have authorization := batch_source_authorized evm out (batchLocals batch) frame values
    (by simp [batchLocals]) (by simp [batchLocals]) run
  have continuity := batch_source_continuity evm out batch frame values run
  have owners := batch_source_after_owners evm out batch frame values ∅ run
  have deposit := batch_source_after_deposit evm out batch frame values ∅ run
  have backing := batch_source_after_backing evm out batch frame values ∅ run
  have claims := batch_source_after_claims evm out batch frame values ∅ run
  have lockGuard := (accepted_require (accepted_require run).2).1
  have lockLoad := eval_entered evm (batchLocals batch) (by simp [batchLocals])
  have unlocked : readWord evm evm.executionEnv.codeOwner ⟨6⟩ = ⟨0⟩ := by
    change evalExpr? config ⟨contract, batchLocals batch⟩ evm
      (.binary .eq (.storage ⟨"entered", []⟩) (.intLit 0)) = .ok (.bool true) at lockGuard
    simp only [evalExpr?, lockLoad, bind, EvalResult.bind, pure, evalBinaryOp?,
      EvalResult.ok.injEq, Value.bool.injEq, beq_iff_eq, Value.int.injEq] at lockGuard
    exact uint256_toNat_eq_zero (by exact_mod_cast lockGuard)
  exact {
    nonpayable := authorization.1
    unlocked := unlocked
    authorized := authorization.2
    numberFits := continuity.1 ▸ continuity.2.1
    nextNumber := continuity.1
    oldRoot := continuity.2.2
    depositOwner := by simpa only [optionalOwner, validOwner, project] using owners.1
    withdrawalOwner := by simpa only [optionalOwner, validOwner, project] using owners.2.1
    depositCovered := deposit.1
    backingFits := backing.1
    withdrawalCovered := backing.2.1
    claimFits := claims.1 }

/-- The source body has an accepted execution exactly when its checks hold. -/
theorem batch_source_success_iff (evm : Ethereum.State) (batch : Batch) :
    (∃ frame out values, ExecTransitionBody config contract evm (batchLocals batch)
      contract.transitions[1]!.body (.returned frame out values)) ↔ BatchExecutionChecks evm batch := by
  constructor
  · rintro ⟨frame, out, values, run⟩
    exact batch_source_checks evm out batch frame values run
  · intro checks
    exact ⟨_, _, _, batch_body_success evm batch checks⟩

end Rollup.EVM
