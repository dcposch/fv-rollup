import proofs.WorldExecution
import proofs.WorldLocalSteps
import proofs.WorldSelfdestruct

open Ethereum Ethereum.EVM

set_option maxRecDepth 2048

namespace Rollup.EVM

/-- At the call depth limit, calls and creation cannot change ETH balances. -/
theorem call_creation_depth_limit_ledger
    {before after : Ethereum.State} {gasCost : Nat} {op : Operation} {arg : Option (UInt256 × Nat)}
    (kind : op = .CREATE ∨ op = .CREATE2 ∨ op = .CALL ∨ op = .CALLCODE ∨
      op = .DELEGATECALL ∨ op = .STATICCALL)
    (depth : before.executionEnv.depth = 1024)
    (run : step gasCost (op, arg) before = .ok after) :
    ethLedger after.accountMap = ethLedger before.accountMap := by
  rcases kind with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [step, call, depth, bind, Except.bind] at run
  all_goals repeat' first | split at run | contradiction
  all_goals
    have same := Except.ok.inj run
    rw [← same]
    rfl

/-- Every opcode protects ETH at the maximum call depth. -/
theorem foreign_step_balances_at_limit (self : Address) : ForeignStepBalances self 1024 := by
  intro before after gasCost instr depth foreign initial run
  rcases instr with ⟨op, arg⟩
  by_cases internal : LocalOperation op
  · have ledger := local_step_ethLedger internal run
    simp only [EthFrame, worldEth, ledger]
    exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  by_cases destroy : op = .SELFDESTRUCT
  · subst op
    exact selfdestruct_step_balances self foreign (LockedWorld.bounded initial) run
  have kind : op = .CREATE ∨ op = .CREATE2 ∨ op = .CALL ∨ op = .CALLCODE ∨
      op = .DELEGATECALL ∨ op = .STATICCALL := by
    cases op <;> rename_i command <;> cases command <;> simp_all [LocalOperation]
  have ledger := call_creation_depth_limit_ledger kind depth run
  simp only [EthFrame, worldEth, ledger]
  exact ⟨Nat.le_refl _, Nat.le_refl _⟩

end Rollup.EVM
