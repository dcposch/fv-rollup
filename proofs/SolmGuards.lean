import semantics.Semantics
import Reasoning.SolmBody
import Reasoning.Storage

open Solm ABI Reasoning.Theory

namespace Rollup.EVM

def lockGuard : Expr := .binary .eq (.storage ⟨"entered", []⟩) (.intLit 0)

theorem lock_guard_false (evm : Ethereum.State) (locals : Store)
    (localFree : locals.get? "entered" = none)
    (locked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨6⟩ = ⟨1⟩) :
    evalExpr? config ⟨contract, locals⟩ evm lockGuard = .ok (.bool false) := by
  have load : evalExpr? config ⟨contract, locals⟩ evm (.storage ⟨"entered", []⟩) =
      .ok (.int 1) := by
    apply evalExpr_storage_scalar_value (er := ⟨"entered", []⟩)
      (t := .int uint256) (loc := wordLoc ⟨6⟩) localFree
    · simp [evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind]
    · rfl
    · rfl
    · change storageLocLoad evm (uint256Loc ⟨6⟩) = .int 1
      rw [storageLocLoad_uint256, locked]
      rfl
  simp only [lockGuard, evalExpr?, load, bind, EvalResult.bind, pure, evalBinaryOp?]
  rfl

theorem require_false_only_reverts {cfg : Config} {frame : Frame} {evm : Ethereum.State}
    {guard : Expr} {rest : List Stmt} {result : ExecResult}
    (falseGuard : evalExpr? cfg frame evm guard = .ok (.bool false))
    (run : ExecBlock cfg frame evm (.require guard :: rest) result) : result = .reverted := by
  cases run with
  | consNormal step _ => cases step; simp_all
  | consRevert => rfl
  | consReturn step => cases step
  | consBreak step => cases step
  | consContinue step => cases step

theorem second_guard_only_reverts {cfg : Config} {frame : Frame} {evm : Ethereum.State}
    {first guard : Expr} {rest : List Stmt} {result : ExecResult}
    (falseGuard : evalExpr? cfg frame evm guard = .ok (.bool false))
    (run : ExecBlock cfg frame evm (.require first :: .require guard :: rest) result) :
    result = .reverted := by
  cases run with
  | consNormal step tail => cases step; exact require_false_only_reverts falseGuard tail
  | consRevert => rfl
  | consReturn step => cases step
  | consBreak step => cases step
  | consContinue step => cases step

theorem func_only_reverts {cfg : Config} {frame : Frame} {evm : Ethereum.State}
    {body : List Stmt} {result : ExecResult}
    (blocks : ∀ result, ExecBlock cfg frame evm body result → result = .reverted)
    (run : ExecFuncBody cfg frame evm body result) : result = .reverted := by
  cases run with
  | execBlockOK block => have h := blocks _ block; cases h
  | execBlockRet block => have h := blocks _ block; cases h
  | execBlockRevert => rfl
  | execBlockBreak block => have h := blocks _ block; cases h
  | execBlockContinue block => have h := blocks _ block; cases h

/-- A locked deposit has no successful execution in Solm. -/
theorem locked_deposit_reverts (evm : Ethereum.State) (locals : Store) (result : ExecResult)
    (localFree : locals.get? "entered" = none)
    (locked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨6⟩ = ⟨1⟩)
    (run : ExecTransitionBody config contract evm locals contract.transitions[0]!.body result) :
    result = .reverted := by
  exact func_only_reverts (fun _ h => require_false_only_reverts
    (lock_guard_false evm locals localFree locked) h) run

/-- A locked batch has no successful execution in Solm. -/
theorem locked_batch_reverts (evm : Ethereum.State) (locals : Store) (result : ExecResult)
    (localFree : locals.get? "entered" = none)
    (locked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨6⟩ = ⟨1⟩)
    (run : ExecTransitionBody config contract evm locals contract.transitions[1]!.body result) :
    result = .reverted := by
  exact func_only_reverts (fun _ h => second_guard_only_reverts
    (lock_guard_false evm locals localFree locked) h) run

/-- A locked withdrawal has no successful execution in Solm. -/
theorem locked_withdrawal_reverts (evm : Ethereum.State) (locals : Store) (result : ExecResult)
    (localFree : locals.get? "entered" = none)
    (locked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨6⟩ = ⟨1⟩)
    (run : ExecTransitionBody config contract evm locals contract.transitions[2]!.body result) :
    result = .reverted := by
  exact func_only_reverts (fun _ h => second_guard_only_reverts
    (lock_guard_false evm locals localFree locked) h) run

end Rollup.EVM
