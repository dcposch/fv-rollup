import proofs.BoundarySurplus
import proofs.DestructionFrame
import proofs.InstructionStep

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- A foreign self-destruct preserves rollup safety and adds only surplus ETH. -/
theorem selfdestruct_boundary_refines {before after : Ethereum.State} {cost : Nat}
    {arg : Option (UInt256 × Nat)} {self : Address} {keys : AccessScope}
    (foreign : self ≠ before.executionEnv.codeOwner)
    (ready : BoundaryReady self before.accountMap keys)
    (safe : Safe (boundaryModel self before.accountMap keys))
    (run : step cost (.SELFDESTRUCT, arg) before = .ok after) :
    BoundaryReady self after.accountMap keys ∧ Safe (boundaryModel self after.accountMap keys) ∧
      CallTrace (boundaryModel self before.accountMap keys) (boundaryModel self after.accountMap keys) := by
  have frame := selfdestruct_step_static run self
  have balances := selfdestruct_step_balances self foreign (BoundaryReady.world ready) run
  obtain ⟨nextReady, effect⟩ := boundary_surplus_frame ready frame balances
  have trace := CallTrace.next CallTrace.initial effect
  exact ⟨nextReady, callTrace_safe safe trace, trace⟩

/-- Instruction validation and execution give the same forced-ETH model step. -/
theorem selfdestruct_instruction_refines {before after : Ethereum.State} {jumps : Array UInt256}
    {arg : Option (UInt256 × Nat)} {ret} {self : Address} {keys : AccessScope}
    (foreign : self ≠ before.executionEnv.codeOwner)
    (ready : BoundaryReady self before.accountMap keys)
    (safe : Safe (boundaryModel self before.accountMap keys))
    (decoded : (decode before.executionEnv.code before.machineState.pc).getD (.STOP, none) =
      (.SELFDESTRUCT, arg))
    (run : Xstep jumps before = .ok (after, ret)) :
    BoundaryReady self after.accountMap keys ∧ Safe (boundaryModel self after.accountMap keys) ∧
      CallTrace (boundaryModel self before.accountMap keys) (boundaryModel self after.accountMap keys) := by
  obtain ⟨checked, cost, stepped, precheck, opcode, accounts⟩ := instruction_account_step decoded run
  have unchanged := precheck_accounts precheck
  have environment := Z_executionEnv_eq precheck
  have checkedForeign : self ≠ checked.executionEnv.codeOwner := by
    simpa only [environment] using foreign
  have checkedReady : BoundaryReady self checked.accountMap keys := by rwa [unchanged]
  have checkedSafe : Safe (boundaryModel self checked.accountMap keys) := by rwa [unchanged]
  have result := selfdestruct_boundary_refines
    (before := { checked with executionEnv.depth := before.executionEnv.depth })
    checkedForeign checkedReady checkedSafe opcode
  simpa only [accounts, unchanged] using result

end Rollup.EVM
