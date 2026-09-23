import semantics.ChildCall
import Reasoning.Reach

open Ethereum Ethereum.EVM Reasoning.Reach

namespace Rollup.EVM

/-- Exact cursor fields used while advancing toward a known outgoing call. -/
def CursorMatches (environment : ExecutionEnv) (cursor : Cursor) (state : Ethereum.State) : Prop :=
  state.executionEnv = environment ∧ state.machineState.pc = cursor.pc ∧
  state.machineState.stack = cursor.stack ∧ state.machineState.memory = cursor.mem ∧
  state.machineState.activeWords = cursor.aw ∧ state.machineState.returnData = cursor.rdata ∧
  (state.createdAccounts, state.accountMap) = cursor.world

/-- An exact intermediate cursor on a prefix that reaches an actual code child. -/
def PrefixCursor (environment : ExecutionEnv) (target child : Ethereum.State) (cursor : Cursor) : Prop :=
  ∃ state, CursorMatches environment cursor state ∧
    ContinuingPrefix (D_J environment.code 0) state target ∧
    ChildCallEntry (D_J environment.code 0) target child

end Rollup.EVM
