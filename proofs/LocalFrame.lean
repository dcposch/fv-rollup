import proofs.WorldLocalSteps
import proofs.CallbackFrame

open Ethereum Ethereum.EVM Reasoning.Theory

set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

namespace Rollup.EVM

/-- A persistent write leaves every other account unchanged. -/
theorem sstore_other_account (state : Ethereum.State) (self : Address) (slot value : UInt256)
    (foreign : self ≠ state.executionEnv.codeOwner) :
    (state.sstore slot value).accountMap.find? self = state.accountMap.find? self := by
  cases found : state.accountMap.find? state.executionEnv.codeOwner with
  | none => simp [Ethereum.State.sstore, Ethereum.State.lookupAccount, found, Option.option]
  | some owner =>
    simp [Ethereum.State.sstore, Ethereum.State.lookupAccount, Ethereum.State.setAccount,
      Ethereum.State.addAccessedStorageKey, found, Option.option,
      accountMap_find?_insert_ne _ _ _ _ foreign]

/-- A transient write leaves every other account unchanged. -/
theorem tstore_other_account (state : Ethereum.State) (self : Address) (slot value : UInt256)
    (foreign : self ≠ state.executionEnv.codeOwner) :
    (state.tstore slot value).accountMap.find? self = state.accountMap.find? self := by
  cases found : state.accountMap.find? state.executionEnv.codeOwner with
  | none => simp [Ethereum.State.tstore, Ethereum.State.lookupAccount, found, Option.option]
  | some owner =>
    simp [Ethereum.State.tstore, Ethereum.State.lookupAccount, Ethereum.State.updateAccount,
      found, Option.option, accountMap_find?_insert_ne _ _ _ _ foreign]

/-- A local opcode in another storage context leaves the rollup account unchanged. -/
theorem local_step_other_account {before after : Ethereum.State} {gasCost : Nat}
    {op : Operation} {arg : Option (UInt256 × Nat)} {self : Address}
    (internal : LocalOperation op) (foreign : self ≠ before.executionEnv.codeOwner)
    (run : step gasCost (op, arg) before = .ok after) :
    after.accountMap.find? self = before.accountMap.find? self := by
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
    calldatacopy, codeCopy, extCodeCopy', evmLogOp, logOp]
  all_goals first
    | exact sstore_other_account _ _ _ _ foreign
    | exact tstore_other_account _ _ _ _ foreign
    | split <;> rfl

end Rollup.EVM
