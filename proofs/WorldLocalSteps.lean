import proofs.WorldStorage

open Ethereum Ethereum.EVM

set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

namespace Rollup.EVM

/-- These opcodes do not call, create, or destroy accounts. -/
def LocalOperation : Operation → Prop
  | .System .CREATE | .System .CREATE2 | .System .CALL | .System .CALLCODE
  | .System .DELEGATECALL | .System .STATICCALL | .System .SELFDESTRUCT => False
  | _ => True

/-- Every local opcode preserves all ETH balances. -/
theorem local_step_ethLedger {before after : Ethereum.State} {gasCost : Nat}
    {op : Operation} {arg : Option (UInt256 × Nat)}
    (internal : LocalOperation op)
    (run : step gasCost (op, arg) before = .ok after) :
    ethLedger after.accountMap = ethLedger before.accountMap := by
  cases op <;> rename_i command <;> cases command <;> simp only [LocalOperation] at internal
  all_goals simp only [step, execUnOp, execBinOp, execTriOp, machineStateOp, executionEnvOp,
    unaryExecutionEnvOp, unaryStateOp, stateOp, binaryMachineStateOp, binaryMachineStateOp',
    ternaryMachineStateOp, binaryStateOp, ternaryCopyOp, quaternaryCopyOp,
    dup, swap, log0Op, log1Op, log2Op, log3Op, log4Op, bind, Except.bind, Id.run] at run
  all_goals repeat' first
    | contradiction
    | (injection run with equality; subst after)
    | split at run
  all_goals try simp [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC,
    Ethereum.State.balance, Ethereum.State.extCodeSize, Ethereum.State.extCodeHash,
    Ethereum.State.sload, Ethereum.State.tload, Ethereum.State.addAccessedAccount,
    Ethereum.State.addAccessedStorageKey, Ethereum.State.lookupAccount,
    calldatacopy, codeCopy, extCodeCopy', evmLogOp, logOp, sstore_ethLedger, tstore_ethLedger]
  all_goals split <;> rfl

end Rollup.EVM
