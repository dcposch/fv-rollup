import proofs.WorldLocalSteps

open Ethereum Ethereum.EVM

set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

namespace Rollup.EVM

/-- Opcode validation and gas charging preserve the created-account set. -/
theorem precheck_created_set {before after : Ethereum.State} {validJumps : Array UInt256}
    {op : Operation} {cost : Nat}
    (run : Z validJumps op before = .ok (after, cost)) :
    after.createdAccounts = before.createdAccounts := by
  unfold Z at run
  by_cases hδ : δ op = none
  · rw [if_pos hδ] at run
    contradiction
  rw [if_neg hδ] at run
  by_cases hstack : before.machineState.stack.length < (δ op).getD 0
  · rw [if_pos hstack] at run
    contradiction
  rw [if_neg hstack] at run
  by_cases hcost₁ : before.machineState.gasAvailable.toNat < memoryExpansionCost before op
  · rw [if_pos hcost₁] at run
    contradiction
  rw [if_neg hcost₁] at run
  set state₁ : Ethereum.State :=
    { before with machineState.gasAvailable :=
        before.machineState.gasAvailable.subNat (memoryExpansionCost before op) } with hstate₁
  by_cases hcost₂ : state₁.machineState.gasAvailable.toNat < C' state₁ op
  · rw [if_pos (by simpa [state₁] using hcost₂)] at run
    contradiction
  rw [if_neg (by simpa [state₁] using hcost₂)] at run
  by_cases hjump :
      op = Operation.JUMP ∧
        Z.notIn state₁.machineState.stack[0]? validJumps = true
  · rw [if_pos (by simpa [state₁] using hjump)] at run
    contradiction
  rw [if_neg (by simpa [state₁] using hjump)] at run
  by_cases hjumpi :
      op = Operation.JUMPI ∧
        state₁.machineState.stack[1]? ≠ some (⟨0⟩ : UInt256) ∧
        Z.notIn state₁.machineState.stack[0]? validJumps = true
  · rw [if_pos (by simpa [state₁] using hjumpi)] at run
    contradiction
  rw [if_neg (by simpa [state₁] using hjumpi)] at run
  by_cases hreturndata :
      op = Operation.RETURNDATACOPY ∧
        (state₁.machineState.stack.getD 1 ⟨0⟩).toNat
          + (state₁.machineState.stack.getD 2 ⟨0⟩).toNat
            > state₁.machineState.returnData.size
  · rw [if_pos (by simpa [state₁] using hreturndata)] at run
    contradiction
  rw [if_neg (by simpa [state₁] using hreturndata)] at run
  by_cases hstackover :
      state₁.machineState.stack.length - (δ op).getD 0 + (α op).getD 0 > 1024
  · rw [if_pos (by simpa [state₁] using hstackover)] at run
    contradiction
  rw [if_neg (by simpa [state₁] using hstackover)] at run
  by_cases hstatic :
      (¬ state₁.executionEnv.perm) ∧
        (op ∈ [.CREATE, .CREATE2, .SSTORE, .SELFDESTRUCT, .LOG0, .LOG1, .LOG2, .LOG3, .LOG4, .TSTORE] ∨
          (op = .CALL ∧ state₁.machineState.stack[2]? ≠ some ⟨0⟩))
  · rw [if_pos (by simpa [state₁] using hstatic)] at run
    contradiction
  rw [if_neg (by simpa [state₁] using hstatic)] at run
  by_cases hsstore :
      (op = .SSTORE) ∧ state₁.machineState.gasAvailable.toNat ≤ GasConstants.Gcallstipend
  · rw [if_pos (by simpa [state₁] using hsstore)] at run
    contradiction
  rw [if_neg (by simpa [state₁] using hsstore)] at run
  by_cases hcreate :
      op.isCreate ∧ state₁.machineState.stack.getD 2 ⟨0⟩ > ⟨49152⟩
  · rw [if_pos (by simpa [state₁] using hcreate)] at run
    contradiction
  rw [if_neg (by simpa [state₁] using hcreate)] at run
  simp at run
  rcases run with ⟨hstate, _hcost⟩
  rw [← hstate]

/-- Local instructions do not create accounts. -/
theorem local_step_created_set {before after : Ethereum.State} {gasCost : Nat}
    {op : Operation} {arg : Option (UInt256 × Nat)}
    (internal : LocalOperation op) (run : step gasCost (op, arg) before = .ok after) :
    after.createdAccounts = before.createdAccounts := by
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
    Ethereum.State.sload, Ethereum.State.tload, Ethereum.State.sstore, Ethereum.State.tstore,
    Ethereum.State.addAccessedAccount, Ethereum.State.addAccessedStorageKey,
    Ethereum.State.lookupAccount, Ethereum.State.setAccount, Ethereum.State.updateAccount,
    calldatacopy, codeCopy, extCodeCopy', evmLogOp, logOp,
    Substate.addAccessedAccount, Substate.addAccessedStorageKey, Option.option]
  all_goals repeat' first | rfl | split

end Rollup.EVM
