import proofs.RollupCallOpcode
import proofs.InstructionStep

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- A checked call instruction into the rollup preserves safety and refines the model. -/
theorem call_instruction_rollup_refines
    {before after checked : Ethereum.State} {jumps : Array UInt256} {cost : Nat}
    {op : Operation} {arg : Option (UInt256 × Nat)} {ret} {site : CallSite}
    {self : Address} {keys : AccessScope}
    (ordinary : self ∉ π) (foreign : self ≠ before.executionEnv.codeOwner)
    (instruction : (decode before.executionEnv.code before.machineState.pc).getD (.STOP, none) = (op, arg))
    (precheck : Z jumps op before = .ok (checked, cost))
    (arguments : CallSite.decode { checked with executionEnv.depth := before.executionEnv.depth }
      cost op = some site)
    (receiver : AccountAddress.ofUInt256 site.recipient = self)
    (ready : BoundaryReady self before.accountMap keys)
    (safe : Safe (boundaryModel self before.accountMap keys))
    (covered : CalldataCovered
      (site.message (callParent { checked with executionEnv.depth := before.executionEnv.depth })).entryState keys)
    (run : Xstep jumps before = .ok (after, ret)) :
    BoundaryReady self after.accountMap keys ∧ Safe (boundaryModel self after.accountMap keys) ∧
      CallTrace (boundaryModel self before.accountMap keys) (boundaryModel self after.accountMap keys) := by
  obtain ⟨actual, actualCost, stepped, actualCheck, opcode, accounts⟩ :=
    instruction_account_step instruction run
  rw [precheck] at actualCheck
  cases Except.ok.inj actualCheck
  have unchanged := precheck_accounts precheck
  have environment := Z_executionEnv_eq precheck
  have checkedForeign : self ≠ checked.executionEnv.codeOwner := by
    simpa only [environment] using foreign
  have checkedReady : BoundaryReady self checked.accountMap keys := by rwa [unchanged]
  have checkedSafe : Safe (boundaryModel self checked.accountMap keys) := by rwa [unchanged]
  have result := call_opcode_rollup_refines
    (before := { checked with executionEnv.depth := before.executionEnv.depth })
    ordinary checkedForeign arguments receiver checkedReady checkedSafe covered opcode
  simpa only [accounts, unchanged] using result

end Rollup.EVM
