import Reasoning.SolmBody

open Solm

namespace Rollup.EVM

/-- Give both an execution and its unique result. -/
structure ExactStmt (cfg : Config) (frame : Frame) (evm : Ethereum.State)
    (stmt : Stmt) (result : ExecResult) : Prop where
  run : ExecStmt cfg frame evm stmt result
  unique : ∀ other, ExecStmt cfg frame evm stmt other → other = result

structure ExactBlock (cfg : Config) (frame : Frame) (evm : Ethereum.State)
    (body : List Stmt) (result : ExecResult) : Prop where
  run : ExecBlock cfg frame evm body result
  unique : ∀ other, ExecBlock cfg frame evm body other → other = result

theorem exact_nil (cfg frame evm) : ExactBlock cfg frame evm [] (.ok frame evm) := by
  refine ⟨.nil, ?_⟩
  intro other run
  cases run
  rfl

theorem exact_cons {cfg frame evm stmt frame' evm' rest result}
    (first : ExactStmt cfg frame evm stmt (.ok frame' evm'))
    (tail : ExactBlock cfg frame' evm' rest result) :
    ExactBlock cfg frame evm (stmt :: rest) result := by
  refine ⟨.consNormal first.run tail.run, ?_⟩
  intro other run
  cases run with
  | consNormal step rest =>
      have h := first.unique _ step
      cases h
      exact tail.unique _ rest
  | consReturn step => have h := first.unique _ step; cases h
  | consRevert step => have h := first.unique _ step; cases h
  | consBreak step => have h := first.unique _ step; cases h
  | consContinue step => have h := first.unique _ step; cases h

theorem exact_require_true {cfg frame evm cond}
    (eval : evalExpr? cfg frame evm cond = .ok (.bool true)) :
    ExactStmt cfg frame evm (.require cond) (.ok frame evm) := by
  refine ⟨.requireTrue eval, ?_⟩
  intro other run
  cases run <;> simp_all

theorem exact_require_false {cfg frame evm cond rest}
    (eval : evalExpr? cfg frame evm cond = .ok (.bool false)) :
    ExactBlock cfg frame evm (.require cond :: rest) .reverted := by
  refine ⟨.consRevert (.requireFalse eval), ?_⟩
  intro other run
  cases run with
  | consNormal step _ => cases step; simp_all
  | consRevert => rfl
  | consReturn step => cases step
  | consBreak step => cases step
  | consContinue step => cases step

theorem exact_function_revert {cfg frame evm body}
    (block : ExactBlock cfg frame evm body .reverted) :
    ExecFuncBody cfg frame evm body .reverted ∧
    ∀ other, ExecFuncBody cfg frame evm body other → other = .reverted := by
  refine ⟨.execBlockRevert block.run, ?_⟩
  intro other run
  cases run with
  | execBlockOK h => have same := block.unique _ h; cases same
  | execBlockRet h => have same := block.unique _ h; cases same
  | execBlockRevert => rfl
  | execBlockBreak h => have same := block.unique _ h; cases same
  | execBlockContinue h => have same := block.unique _ h; cases same

theorem exact_assign {cfg frame evm origin slot expr value frame' evm'}
    (eval : evalExpr? cfg frame evm expr = .ok value)
    (assign : assignStorageRef? cfg frame evm origin slot value = .ok (frame', evm')) :
    ExactStmt cfg frame evm (.assign origin slot expr) (.ok frame' evm') := by
  refine ⟨.assign eval assign, ?_⟩
  intro other run
  cases run <;> simp_all

theorem exact_let {cfg frame evm name ty expr value}
    (eval : evalExpr? cfg frame evm expr = .ok value) :
    ExactStmt cfg frame evm (.letDecl name ty expr)
      (.ok { frame with locals := frame.locals.insert name value } evm) := by
  refine ⟨.letDecl eval, ?_⟩
  intro other run
  cases run <;> simp_all

theorem exact_function {cfg frame evm body frame' evm'}
    (block : ExactBlock cfg frame evm body (.ok frame' evm')) :
    ExecFuncBody cfg frame evm body (.returned frame' evm' none) ∧
    ∀ other, ExecFuncBody cfg frame evm body other → other = .returned frame' evm' none := by
  refine ⟨.execBlockOK block.run, ?_⟩
  intro other run
  cases run with
  | execBlockOK h => have same := block.unique _ h; cases same; rfl
  | execBlockRet h => have same := block.unique _ h; cases same
  | execBlockRevert h => have same := block.unique _ h; cases same
  | execBlockBreak h => have same := block.unique _ h; cases same
  | execBlockContinue h => have same := block.unique _ h; cases same

/-- These statements can fall through or revert. They cannot return or jump. -/
def plainStmt : Stmt → Bool
  | .require _ | .assign _ _ _ | .letDecl _ _ _ | .lowLevelCall .. => true
  | _ => false

def normalOrReverted : ExecResult → Prop
  | .ok .. | .reverted => True
  | _ => False

theorem plain_stmt_control {cfg frame evm stmt result}
    (plain : plainStmt stmt = true) (run : ExecStmt cfg frame evm stmt result) :
    normalOrReverted result := by
  cases run <;> simp_all [plainStmt, normalOrReverted]

theorem plain_block_control {cfg frame evm body result}
    (plain : body.all plainStmt = true) (run : ExecBlock cfg frame evm body result) :
    normalOrReverted result := by
  induction body generalizing frame evm result with
  | nil => cases run; trivial
  | cons stmt rest ih =>
    have both : plainStmt stmt = true ∧ rest.all plainStmt = true := by simpa using plain
    cases run with
    | consNormal step tail => exact ih both.2 tail
    | consRevert => trivial
    | consReturn step => exact plain_stmt_control both.1 step
    | consBreak step => exact plain_stmt_control both.1 step
    | consContinue step => exact plain_stmt_control both.1 step

theorem plain_function_success {cfg frame evm body frame' evm' values}
    (plain : body.all plainStmt = true)
    (run : ExecFuncBody cfg frame evm body (.returned frame' evm' values)) :
    values = none ∧ ExecBlock cfg frame evm body (.ok frame' evm') := by
  cases run with
  | execBlockOK block => exact ⟨rfl, block⟩
  | execBlockRet block => exact (plain_block_control plain block).elim
  | execBlockBreak block => exact (plain_block_control plain block).elim
  | execBlockContinue block => exact (plain_block_control plain block).elim

theorem split_block_success {cfg frame evm headBody suffix frame' evm'}
    (run : ExecBlock cfg frame evm (headBody ++ suffix) (.ok frame' evm')) :
    ∃ middle before, ExecBlock cfg frame evm headBody (.ok middle before) ∧
      ExecBlock cfg middle before suffix (.ok frame' evm') := by
  induction headBody generalizing frame evm with
  | nil => exact ⟨frame, evm, .nil, run⟩
  | cons stmt rest ih =>
      cases run with
      | consNormal step tail =>
          obtain ⟨middle, before, left, right⟩ := ih tail
          exact ⟨middle, before, .consNormal step left, right⟩

theorem storage_assign_frame {cfg frame evm slot value frame' evm'}
    (assign : assignStorageRef? cfg frame evm .storage slot value = .ok (frame', evm')) :
    frame' = frame := by
  unfold assignStorageRef? at assign
  cases hresolve : resolveStorageRef? cfg frame evm slot <;>
    simp only [hresolve, bind, EvalResult.bind] at assign
  all_goals try contradiction
  rename_i resolved
  obtain ⟨reference, ty⟩ := resolved
  cases value <;>
    simp only [EvalResult.ofOption, pure] at assign
  all_goals
    repeat (first | contradiction | (split at assign <;> simp_all))

def localUntouched (name : String) : Stmt → Bool
  | .require _ | .assign .storage _ _ => true
  | .letDecl written _ _ => written != name
  | _ => false

theorem stmt_preserves_local {cfg frame evm stmt frame' evm'} (name : String)
    (protects : localUntouched name stmt = true)
    (run : ExecStmt cfg frame evm stmt (.ok frame' evm')) :
    frame'.locals.get? name = frame.locals.get? name := by
  cases run <;> simp only [localUntouched] at protects
  all_goals try contradiction
  case requireTrue => rfl
  case letDecl =>
    exact Reasoning.Theory.store_get_ne _ _ (by simpa using protects)
  case assign expression value origin slot eval assign =>
    cases origin with
    | localVar => contradiction
    | storage => rw [storage_assign_frame assign]

theorem block_preserves_local {cfg frame evm body frame' evm'} (name : String)
    (protects : body.all (localUntouched name) = true)
    (run : ExecBlock cfg frame evm body (.ok frame' evm')) :
    frame'.locals.get? name = frame.locals.get? name := by
  induction body generalizing frame evm with
  | nil => cases run; rfl
  | cons stmt rest ih =>
    have both : localUntouched name stmt = true ∧ rest.all (localUntouched name) = true :=
      by simpa using protects
    cases run with
    | consNormal first tail =>
      exact (ih both.2 tail).trans (stmt_preserves_local name both.1 first)

theorem accepted_require {cfg frame evm guard rest frame' evm' values}
    (run : ExecFuncBody cfg frame evm (.require guard :: rest)
      (.returned frame' evm' values)) :
    evalExpr? cfg frame evm guard = .ok (.bool true) ∧
      ExecFuncBody cfg frame evm rest (.returned frame' evm' values) := by
  cases run <;> rename_i block
  all_goals cases block <;> cases_type ExecStmt
  all_goals constructor
  all_goals first
    | assumption
    | exact .execBlockOK (by assumption)
    | exact .execBlockRet (by assumption)
    | exact .execBlockBreak (by assumption)
    | exact .execBlockContinue (by assumption)

theorem accepted_assign {cfg frame evm origin slot expr rest frame' evm' values value middleFrame middleState}
    (eval : evalExpr? cfg frame evm expr = .ok value)
    (assign : assignStorageRef? cfg frame evm origin slot value = .ok (middleFrame, middleState))
    (run : ExecFuncBody cfg frame evm (.assign origin slot expr :: rest)
      (.returned frame' evm' values)) :
    ExecFuncBody cfg middleFrame middleState rest (.returned frame' evm' values) := by
  have exactStep := exact_assign eval assign
  cases run <;> rename_i block
  all_goals cases block
  all_goals have same := exactStep.unique _ (by assumption)
  all_goals cases same
  all_goals first
    | exact .execBlockOK (by assumption)
    | exact .execBlockRet (by assumption)
    | exact .execBlockBreak (by assumption)
    | exact .execBlockContinue (by assumption)


theorem accepted_exact {cfg frame evm stmt rest frame' evm' values middleFrame middleState}
    (step : ExactStmt cfg frame evm stmt (.ok middleFrame middleState))
    (run : ExecFuncBody cfg frame evm (stmt :: rest) (.returned frame' evm' values)) :
    ExecFuncBody cfg middleFrame middleState rest (.returned frame' evm' values) := by
  cases run <;> rename_i block
  all_goals cases block
  all_goals have same := step.unique _ (by assumption)
  all_goals cases same
  all_goals first
    | exact .execBlockOK (by assumption)
    | exact .execBlockRet (by assumption)
    | exact .execBlockBreak (by assumption)
    | exact .execBlockContinue (by assumption)

end Rollup.EVM
