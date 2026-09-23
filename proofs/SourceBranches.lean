import proofs.SourceSteps

open Solm
namespace Rollup.EVM

private theorem require_block_classify {cfg frame evm guard result}
    (run : ExecBlock cfg frame evm [.require guard] result) :
    result = .reverted ∨
      (result = .ok frame evm ∧ evalExpr? cfg frame evm guard = .ok (.bool true)) := by
  cases run <;> cases_type ExecStmt
  all_goals first | exact Or.inl rfl | skip
  cases_type ExecBlock
  exact Or.inr ⟨rfl, by assumption⟩

private theorem require_branch_classify {cfg frame evm cond yes no result}
    (run : ExecStmt cfg frame evm (.ite cond [.require yes] [.require no]) result) :
    result = .reverted ∨ (result = .ok frame evm ∧
      ((evalExpr? cfg frame evm cond = .ok (.bool true) ∧
        evalExpr? cfg frame evm yes = .ok (.bool true)) ∨
       (evalExpr? cfg frame evm cond = .ok (.bool false) ∧
        evalExpr? cfg frame evm no = .ok (.bool true)))) := by
  cases run with
  | iteTrue test branch =>
    rcases require_block_classify branch with reverted | ⟨same, checked⟩
    · exact Or.inl reverted
    · exact Or.inr ⟨same, Or.inl ⟨test, checked⟩⟩
  | iteFalse test branch =>
    rcases require_block_classify branch with reverted | ⟨same, checked⟩
    · exact Or.inl reverted
    · exact Or.inr ⟨same, Or.inr ⟨test, checked⟩⟩
  | iteCondRevert => exact Or.inl rfl

theorem accepted_require_branch {cfg frame evm cond yes no rest frame' evm' values}
    (run : ExecFuncBody cfg frame evm (.ite cond [.require yes] [.require no] :: rest)
      (.returned frame' evm' values)) :
    ((evalExpr? cfg frame evm cond = .ok (.bool true) ∧
      evalExpr? cfg frame evm yes = .ok (.bool true)) ∨
     (evalExpr? cfg frame evm cond = .ok (.bool false) ∧
      evalExpr? cfg frame evm no = .ok (.bool true))) ∧
    ExecFuncBody cfg frame evm rest (.returned frame' evm' values) := by
  cases run <;> rename_i block
  all_goals cases block
  all_goals rcases require_branch_classify (by assumption) with reverted | ⟨same, checked⟩
  all_goals first | cases reverted | cases same
  all_goals refine ⟨checked, ?_⟩
  all_goals first
    | exact .execBlockOK (by assumption)
    | exact .execBlockRet (by assumption)
    | exact .execBlockBreak (by assumption)
    | exact .execBlockContinue (by assumption)
end Rollup.EVM
