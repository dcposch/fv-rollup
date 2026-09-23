import proofs.PrefixCursor

open Ethereum Ethereum.EVM Reasoning.Reach

namespace Rollup.EVM

/-- Restoring the caller depth retains an exact cursor with the same environment. -/
theorem cursor_matches_restore_depth {environment : ExecutionEnv} {cursor : Cursor}
    {before after : Ethereum.State} (beforeEnvironment : before.executionEnv = environment)
    (matched : CursorMatches environment cursor after) :
    CursorMatches environment cursor { after with executionEnv.depth := before.executionEnv.depth } := by
  refine ⟨?_, matched.2⟩
  change { after.executionEnv with depth := before.executionEnv.depth } = environment
  rw [matched.1, beforeEnvironment]

/-- A known future child excludes the gas-error branch of each preceding instruction. -/
theorem prefix_cursor_guarded {environment : ExecutionEnv} {target child : Ethereum.State}
    {cursor next : Cursor} {op : Operation} {arg : Option (UInt256 × Nat)}
    (reached : PrefixCursor environment target child cursor)
    (decoded : (decode environment.code cursor.pc).getD (.STOP, none) = (op, arg))
    (noncall : op ≠ .CALL ∧ op ≠ .CALLCODE ∧ op ≠ .DELEGATECALL ∧ op ≠ .STATICCALL)
    (blocked : Ethereum.State → Prop) [∀ state, Decidable (blocked state)]
    (nextState : Ethereum.State → Ethereum.State)
    (execution : ∀ state, CursorMatches environment cursor state →
      Xstep (D_J environment.code 0) state =
        if blocked state then .error .OutOfGass else .ok (nextState state, none))
    (effect : ∀ state, CursorMatches environment cursor state →
      CursorMatches environment next (nextState state)) :
    PrefixCursor environment target child next := by
  apply prefix_cursor_step reached decoded noncall
  intro before after matched run
  rw [execution before matched] at run
  split at run <;> try contradiction
  have same := congrArg Prod.fst (Except.ok.inj run)
  dsimp only at same
  subst after
  exact cursor_matches_restore_depth matched.1 (effect before matched)

end Rollup.EVM
