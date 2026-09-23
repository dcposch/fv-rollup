import semantics.ChildCall
import proofs.CallOpcode

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- An actual foreign child entry preserves the reservation throughout its frame. -/
theorem child_call_prefix_safe {before child current : Ethereum.State}
    {jumps : Array UInt256} {self : Address} (keys : AccessScope) (payment : Payment)
    (entered : ChildCallEntry jumps before child)
    (foreign : self ≠ before.executionEnv.codeOwner)
    (childForeign : self ≠ child.executionEnv.codeOwner)
    (initial : LockedWorld self before.accountMap)
    (safe : Safe (inFlightProjection before self keys payment))
    (trace : InstructionPrefix (D_J child.executionEnv.code 0) child current) :
    LockedWorld self current.accountMap ∧ Safe (inFlightProjection current self keys payment) := by
  cases entered with
  | @entered op arg checked cost site code instruction precheck arguments enabled selected =>
    have accounts := precheck_accounts precheck
    have environment := Z_executionEnv_eq precheck
    have checkedForeign : self ≠ checked.executionEnv.codeOwner := by
      simpa only [environment] using foreign
    have checkedInitial : LockedWorld self checked.accountMap := by rwa [accounts]
    have checkedSafe : Safe (inFlightProjection
        { checked with executionEnv.depth := before.executionEnv.depth } self keys payment) := by
      simpa only [inFlightProjection, project_boundary, accounts] using safe
    exact call_opcode_prefix_safe keys payment code arguments enabled checkedForeign childForeign
      checkedInitial checkedSafe trace

end Rollup.EVM
