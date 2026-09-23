import proofs.support.AccountOperations
import semantics.CallOpcode
import semantics.CreationSite
import proofs.InstructionStep

open Ethereum Ethereum.EVM

set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

namespace Rollup.EVM

/-- Every opcode in the account-preserving set leaves the full account map fixed. -/
theorem account_preserving_step {before after : Ethereum.State} {cost : Nat}
    {op : Operation} {arg : Option (UInt256 × Nat)}
    (neutral : AccountPreservingOperation op)
    (run : step cost (op, arg) before = .ok after) : after.accountMap = before.accountMap := by
  cases op <;> rename_i command <;> cases command <;> simp only [AccountPreservingOperation] at neutral
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
  all_goals split <;> rfl

/-- Instruction checks and an account-preserving opcode leave accounts fixed. -/
theorem account_preserving_instruction {before after : Ethereum.State} {jumps : Array UInt256}
    {op : Operation} {arg : Option (UInt256 × Nat)} {ret}
    (neutral : AccountPreservingOperation op)
    (decoded : (decode before.executionEnv.code before.machineState.pc).getD (.STOP, none) = (op, arg))
    (run : Xstep jumps before = .ok (after, ret)) : after.accountMap = before.accountMap := by
  obtain ⟨checked, cost, stepped, precheck, opcode, accounts⟩ := instruction_account_step decoded run
  have opcodeAccounts : stepped.accountMap = checked.accountMap :=
    account_preserving_step
      (before := { checked with executionEnv.depth := before.executionEnv.depth }) neutral opcode
  exact accounts.trans (opcodeAccounts.trans (precheck_accounts precheck))

/-- No opcode in this set can enter a call or creation frame. -/
theorem account_preserving_no_child (state : Ethereum.State) (cost : Nat) (op : Operation)
    (neutral : AccountPreservingOperation op) :
    CallSite.decode state cost op = none ∧ CreationSite.decode state op = none := by
  cases op <;> rename_i command <;> cases command <;>
    simp_all [AccountPreservingOperation, CallSite.decode, CreationSite.decode]

end Rollup.EVM
