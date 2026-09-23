import proofs.support.PrefixCursor
import proofs.PrefixHead

open Ethereum Ethereum.EVM Reasoning.Reach

namespace Rollup.EVM

/-- Start the exact cursor from an actual prefix to a code child. -/
theorem prefix_cursor_initial {start target child : Ethereum.State}
    (trace : ContinuingPrefix (D_J start.executionEnv.code 0) start target)
    (entered : ChildCallEntry (D_J start.executionEnv.code 0) target child) :
    PrefixCursor start.executionEnv target child
      ⟨start.machineState.pc, start.machineState.stack, start.machineState.memory,
        start.machineState.activeWords, start.machineState.returnData,
        start.createdAccounts, start.accountMap⟩ :=
  ⟨start, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, trace, entered⟩

/-- Advance an exact cursor through one non-call instruction on the actual prefix. -/
theorem prefix_cursor_step {environment : ExecutionEnv} {target child : Ethereum.State}
    {cursor next : Cursor} {op : Operation} {arg : Option (UInt256 × Nat)}
    (reached : PrefixCursor environment target child cursor)
    (decoded : (decode environment.code cursor.pc).getD (.STOP, none) = (op, arg))
    (noncall : op ≠ .CALL ∧ op ≠ .CALLCODE ∧ op ≠ .DELEGATECALL ∧ op ≠ .STATICCALL)
    (effect : ∀ before after, CursorMatches environment cursor before →
      Xstep (D_J environment.code 0) before = .ok (after, none) →
      CursorMatches environment next { after with executionEnv.depth := before.executionEnv.depth }) :
    PrefixCursor environment target child next := by
  obtain ⟨before, matchesCursor, trace, entered⟩ := reached
  have actual : (decode before.executionEnv.code before.machineState.pc).getD (.STOP, none) = (op, arg) := by
    rw [matchesCursor.1, matchesCursor.2.1]
    exact decoded
  obtain ⟨after, run, rest⟩ := noncall_prefix_head actual noncall trace entered
  exact ⟨_, effect before after matchesCursor run, rest, entered⟩

/-- A cursor that cannot continue cannot precede the known child entry. -/
theorem prefix_cursor_stopped {environment : ExecutionEnv} {target child : Ethereum.State}
    {cursor : Cursor} {op : Operation} {arg : Option (UInt256 × Nat)}
    (reached : PrefixCursor environment target child cursor)
    (decoded : (decode environment.code cursor.pc).getD (.STOP, none) = (op, arg))
    (noncall : op ≠ .CALL ∧ op ≠ .CALLCODE ∧ op ≠ .DELEGATECALL ∧ op ≠ .STATICCALL)
    (stopped : ∀ before after, CursorMatches environment cursor before →
      Xstep (D_J environment.code 0) before ≠ .ok (after, none)) : False := by
  obtain ⟨before, matchesCursor, trace, entered⟩ := reached
  have actual : (decode before.executionEnv.code before.machineState.pc).getD (.STOP, none) = (op, arg) := by
    rw [matchesCursor.1, matchesCursor.2.1]
    exact decoded
  obtain ⟨after, run, rest⟩ := noncall_prefix_head actual noncall trace entered
  exact stopped before after matchesCursor run

/-- A symbolic output word can be chosen from the actual instruction result. -/
theorem prefix_cursor_step_exists {environment : ExecutionEnv} {target child : Ethereum.State}
    {cursor : Cursor} {op : Operation} {arg : Option (UInt256 × Nat)} {α : Type} (next : α → Cursor)
    (reached : PrefixCursor environment target child cursor)
    (decoded : (decode environment.code cursor.pc).getD (.STOP, none) = (op, arg))
    (noncall : op ≠ .CALL ∧ op ≠ .CALLCODE ∧ op ≠ .DELEGATECALL ∧ op ≠ .STATICCALL)
    (effect : ∀ before after, CursorMatches environment cursor before →
      Xstep (D_J environment.code 0) before = .ok (after, none) →
      ∃ value, CursorMatches environment (next value)
        { after with executionEnv.depth := before.executionEnv.depth }) :
    ∃ value, PrefixCursor environment target child (next value) := by
  obtain ⟨before, matchesCursor, trace, entered⟩ := reached
  have actual : (decode before.executionEnv.code before.machineState.pc).getD (.STOP, none) = (op, arg) := by
    rw [matchesCursor.1, matchesCursor.2.1]
    exact decoded
  obtain ⟨after, run, rest⟩ := noncall_prefix_head actual noncall trace entered
  obtain ⟨value, matchNext⟩ := effect before after matchesCursor run
  exact ⟨value, _, matchNext, rest, entered⟩

end Rollup.EVM
