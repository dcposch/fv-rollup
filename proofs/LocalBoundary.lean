import proofs.LocalFrame
import proofs.BoundarySurplus
import proofs.InstructionStep

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- Local instructions in another account preserve the complete rollup model. -/
theorem local_step_boundary {before after : Ethereum.State} {cost : Nat}
    {op : Operation} {arg : Option (UInt256 × Nat)} {self : Address} {keys : AccessScope}
    (internal : LocalOperation op) (foreign : self ≠ before.executionEnv.codeOwner)
    (ready : BoundaryReady self before.accountMap keys)
    (run : step cost (op, arg) before = .ok after) :
    BoundaryReady self after.accountMap keys ∧
      boundaryModel self after.accountMap keys = boundaryModel self before.accountMap keys := by
  have account := local_step_other_account internal foreign run
  have lookup : after.accountMap.findD self default = before.accountMap.findD self default := by
    simp only [Batteries.RBMap.findD, account]
  have frame : CodeStorageFrame self before.accountMap after.accountMap := by
    simp only [CodeStorageFrame, lookup, and_self]
  have ledger := local_step_ethLedger internal run
  have balances : EthFrame self before.accountMap after.accountMap := by
    simp only [EthFrame, worldEth, ledger, le_refl, and_self]
  have next := (boundary_surplus_frame ready frame balances).1
  have projected := CodeStorageFrame.project
    (before := accountView self before.accountMap) (after := accountView self after.accountMap) frame keys
  have eth : (boundaryModel self after.accountMap keys).eth =
      (boundaryModel self before.accountMap keys).eth := by
    simp only [boundaryModel, project_ethLedger, accountView, ledger]
  change boundaryModel self after.accountMap keys =
    { boundaryModel self before.accountMap keys with eth := (boundaryModel self after.accountMap keys).eth } at projected
  rw [eth] at projected
  exact ⟨next, projected⟩

/-- Validation and a local opcode preserve the rollup between calls. -/
theorem local_instruction_boundary {before after : Ethereum.State} {jumps : Array UInt256}
    {op : Operation} {arg : Option (UInt256 × Nat)} {ret} {self : Address} {keys : AccessScope}
    (internal : LocalOperation op) (foreign : self ≠ before.executionEnv.codeOwner)
    (ready : BoundaryReady self before.accountMap keys)
    (decoded : (decode before.executionEnv.code before.machineState.pc).getD (.STOP, none) = (op, arg))
    (run : Xstep jumps before = .ok (after, ret)) :
    BoundaryReady self after.accountMap keys ∧
      boundaryModel self after.accountMap keys = boundaryModel self before.accountMap keys := by
  obtain ⟨checked, cost, stepped, precheck, opcode, accounts⟩ := instruction_account_step decoded run
  have unchanged := precheck_accounts precheck
  have environment := Z_executionEnv_eq precheck
  have checkedForeign : self ≠ checked.executionEnv.codeOwner := by
    simpa only [environment] using foreign
  have checkedReady : BoundaryReady self checked.accountMap keys := by rwa [unchanged]
  have result := local_step_boundary
    (before := { checked with executionEnv.depth := before.executionEnv.depth })
    internal checkedForeign checkedReady opcode
  simpa only [accounts, unchanged] using result

end Rollup.EVM
