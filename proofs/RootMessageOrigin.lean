import proofs.support.RootMessageOrigin
import proofs.RootEntryBoundary
import proofs.RollupCallSite

open Ethereum Ethereum.EVM

set_option maxRecDepth 4096

namespace Rollup.EVM

/-- An actual child entry into the rollup retains its funded pre-transfer message. -/
theorem child_root_message_origin {before child : Ethereum.State} {jumps : Array UInt256} {self keys}
    (entered : ChildCallEntry jumps before child) (foreign : self ≠ before.executionEnv.codeOwner)
    (ready : BoundaryReady self before.accountMap keys) (safe : Safe (boundaryModel self before.accountMap keys))
    (owner : child.executionEnv.codeOwner = self) : RootMessageOrigin self keys child := by
  cases entered with
  | @entered op arg checked cost site code instruction precheck arguments enabled selected =>
    have accounts := precheck_accounts precheck
    have environment := Z_executionEnv_eq precheck
    have checkedForeign : self ≠ checked.executionEnv.codeOwner := by simpa only [environment] using foreign
    have checkedReady : BoundaryReady self checked.accountMap keys :=
      Eq.mpr (congrArg (fun world => BoundaryReady self world keys) accounts) ready
    have checkedSafe : Safe (boundaryModel self checked.accountMap keys) :=
      Eq.mpr (congrArg (fun world => Safe (boundaryModel self world keys)) accounts) safe
    have receiver : AccountAddress.ofUInt256 site.recipient = self := owner
    have target := call_opcode_target checkedForeign arguments receiver
    rw [target] at selected
    have pinned := selected_pinned_code (BoundaryReady.pinned checkedReady) selected
    subst code
    exact ⟨site.message (callParent { checked with executionEnv.depth := before.executionEnv.depth }),
      rfl, call_opcode_rollup_environment checkedForeign arguments receiver enabled, checkedReady, checkedSafe⟩

/-- Foreign frame paths preserve the message binding at their first active root invocation. -/
theorem root_entry_message_origin {self keys root start}
    (path : CoveredRootEntryPath self keys root start) (ordinary : self ∉ π)
    (ready : BoundaryReady self start.accountMap keys) (safe : Safe (boundaryModel self start.accountMap keys))
    (origin : start.executionEnv.codeOwner = self → RootMessageOrigin self keys start) :
    RootMessageOrigin self keys root := by
  induction path with
  | here owner code covered => exact origin owner
  | call foreign earlier entered rest ih =>
    have first := continuing_prefix_boundary earlier ordinary foreign ready safe
    have environment := continuing_prefix_environment (covered_prefix_execution earlier)
    have beforeForeign := ne_of_ne_of_eq foreign (congrArg ExecutionEnv.codeOwner environment).symm
    have next := child_call_entry_boundary entered beforeForeign first.1 first.2.1
    exact ih next.1 next.2.1 (child_root_message_origin entered beforeForeign first.1 first.2.1)
  | creation foreign earlier entered rest ih =>
    have first := continuing_prefix_boundary earlier ordinary foreign ready safe
    have environment := continuing_prefix_environment (covered_prefix_execution earlier)
    have beforeForeign := ne_of_ne_of_eq foreign (congrArg ExecutionEnv.codeOwner environment).symm
    rcases child_creation_entry_boundary entered beforeForeign first.1 first.2.1 with
      ⟨invalid, zero⟩ | ⟨childForeign, next⟩
    · exact False.elim (root_entry_invalid (covered_root_entry_execution rest) invalid zero)
    · exact ih next.1 next.2.1 (fun same => False.elim (childForeign same.symm))

end Rollup.EVM
