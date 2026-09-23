import proofs.WorldLocalSteps
import proofs.CallbackFrame

open Ethereum Ethereum.EVM

set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

namespace Rollup.EVM

/-- Persistent writes preserve every account's code. -/
theorem sstore_code (evm : Ethereum.State) (slot value : UInt256) :
    accountCodeStateEq evm.accountMap (evm.sstore slot value).accountMap := by
  unfold Ethereum.State.sstore
  cases found : evm.lookupAccount evm.executionEnv.codeOwner with
  | none => simp [found, Option.option, accountCodeStateEq]
  | some account =>
    simp only [found, Option.option, Ethereum.State.setAccount, Ethereum.State.addAccessedStorageKey]
    apply accountCodeStateEq_insert_preserve
    have old : (evm.accountMap.findD evm.executionEnv.codeOwner default).code = account.code := by
      simp only [Ethereum.State.lookupAccount] at found
      simp [Batteries.RBMap.findD, found]
    rw [old]
    unfold Account.updateStorage
    split <;> rfl

/-- Transient writes preserve every account's code. -/
theorem tstore_code (evm : Ethereum.State) (slot value : UInt256) :
    accountCodeStateEq evm.accountMap (evm.tstore slot value).accountMap := by
  unfold Ethereum.State.tstore
  cases found : evm.lookupAccount evm.executionEnv.codeOwner with
  | none => simp [found, Option.option, accountCodeStateEq]
  | some account =>
    simp only [found, Option.option, Ethereum.State.updateAccount]
    apply accountCodeStateEq_insert_preserve
    have old : (evm.accountMap.findD evm.executionEnv.codeOwner default).code = account.code := by
      simp only [Ethereum.State.lookupAccount] at found
      simp [Batteries.RBMap.findD, found]
    rw [old]
    unfold Account.updateTransientStorage
    split <;> rfl

private theorem sstore_code_read (evm : Ethereum.State) (slot value : UInt256) (owner : AccountAddress) :
    ((evm.sstore slot value).accountMap.findD owner default).code =
      (evm.accountMap.findD owner default).code := (sstore_code evm slot value owner).symm

private theorem tstore_code_read (evm : Ethereum.State) (slot value : UInt256) (owner : AccountAddress) :
    ((evm.tstore slot value).accountMap.findD owner default).code =
      (evm.accountMap.findD owner default).code := (tstore_code evm slot value owner).symm

/-- No local opcode can change account code, in any storage context. -/
theorem local_step_code {before after : Ethereum.State} {gasCost : Nat}
    {op : Operation} {arg : Option (UInt256 × Nat)}
    (internal : LocalOperation op) (run : step gasCost (op, arg) before = .ok after) :
    accountCodeStateEq before.accountMap after.accountMap := by
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
    calldatacopy, codeCopy, extCodeCopy', evmLogOp, logOp, accountCodeStateEq, sstore_code_read, tstore_code_read]
  all_goals split <;> intro addr <;> rfl

end Rollup.EVM
