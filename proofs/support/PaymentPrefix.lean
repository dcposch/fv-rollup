import proofs.support.WithdrawalChecks
import semantics.ChildCall

open Ethereum Ethereum.EVM Reasoning.Theory

namespace Rollup.EVM

/-- The withdrawal cursor before its outgoing CALL. No payment has completed yet. -/
def WithdrawalCallPrefix (start cursor : Ethereum.State) : Prop :=
  WithdrawalBytecodeChecks start.accountMap start.executionEnv ∧
  solcSelectorWord start.executionEnv = ⟨0xbb3ef682⟩ ∧
  cursor.accountMap = sstoreAccountMap start.executionEnv.codeOwner start.accountMap ⟨6⟩ ⟨1⟩ ∧
  cursor.executionEnv = start.executionEnv ∧ cursor.machineState.pc = ⟨935⟩ ∧
  ∃ gas,
    cursor.machineState.stack =
      [gas, calldataWord start.executionEnv.calldata 4, calldataWord start.executionEnv.calldata 36,
        ⟨128⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩,
        ⟨128⟩, calldataWord start.executionEnv.calldata 36, calldataWord start.executionEnv.calldata 4, ⟨0⟩,
        withdrawalClaimWord (sstoreAccountMap start.executionEnv.codeOwner start.accountMap ⟨6⟩ ⟨1⟩)
          start.executionEnv,
        calldataWord start.executionEnv.calldata 36, calldataWord start.executionEnv.calldata 4,
        ⟨226⟩, ⟨0xbb3ef682⟩]

/-- Open target: every actual outgoing code call reaches the checked withdrawal cursor.
    This includes parents whose final result is a revert or an execution error. -/
def RootCallPrefixBound : Prop :=
  ∀ created genesis blocks accounts original substate (environment : ExecutionEnv) (gas : Sat256)
    (cursor child : Ethereum.State),
    environment.code = runtimeBytecode → environment.calldata.size < UInt256.size →
    let start := initState created genesis blocks accounts original gas substate environment
    ContinuingPrefix (D_J runtimeBytecode 0) start cursor →
    ChildCallEntry (D_J runtimeBytecode 0) cursor child → WithdrawalCallPrefix start cursor

end Rollup.EVM
