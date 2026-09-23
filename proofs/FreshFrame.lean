import proofs.support.FreshFrame
import proofs.ActiveCallEntry
import proofs.RollupCallSite

open Ethereum Ethereum.EVM Reasoning.Theory

namespace Rollup.EVM

/-- A selected message starts a fresh code frame. -/
theorem message_code_entry_fresh (call : MessageCall) (code : ByteArray) : FreshFrame (call.codeEntry code) := rfl

/-- Creation starts a fresh initialization frame. -/
theorem creation_entry_fresh (call : CreationCall) : FreshFrame call.entryState := rfl

/-- Every actual call child is a fresh frame. -/
theorem child_call_entry_fresh {before child : Ethereum.State} {jumps : Array UInt256}
    (entered : ChildCallEntry jumps before child) : FreshFrame child := by
  cases entered
  rfl

/-- Every actual creation child is a fresh frame. -/
theorem child_creation_entry_fresh {before child : Ethereum.State} {jumps : Array UInt256}
    (entered : ChildCreationEntry jumps before child) : FreshFrame child := by
  cases entered
  rfl

/-- The calldata of a code-call child fits in an EVM word. -/
theorem child_call_entry_bounded {before child : Ethereum.State} {jumps : Array UInt256}
    (entered : ChildCallEntry jumps before child) : child.executionEnv.calldata.size < UInt256.size := by
  cases entered with
  | entered instruction precheck arguments enabled selected => exact call_site_calldata_bound _ _

/-- Initialization has empty calldata. -/
theorem child_creation_entry_bounded {before child : Ethereum.State} {jumps : Array UInt256}
    (entered : ChildCreationEntry jumps before child) : child.executionEnv.calldata.size < UInt256.size := by
  cases entered
  change ByteArray.empty.size < UInt256.size
  decide +kernel

/-- A child in the rollup's storage context selects its pinned runtime code. -/
theorem child_call_entry_pinned {before child : Ethereum.State} {jumps : Array UInt256} {self : Address}
    (entered : ChildCallEntry jumps before child) (foreign : self ≠ before.executionEnv.codeOwner)
    (pinned : (before.accountMap.findD self default).code = runtimeBytecode)
    (owner : child.executionEnv.codeOwner = self) : child.executionEnv.code = runtimeBytecode := by
  cases entered with
  | @entered op arg checked cost site code instruction precheck arguments enabled selected =>
    have accounts := precheck_accounts precheck
    have environment := Z_executionEnv_eq precheck
    have checkedForeign : self ≠ checked.executionEnv.codeOwner := by simpa only [environment] using foreign
    have receiver : AccountAddress.ofUInt256 site.recipient = self := owner
    have target := call_opcode_target checkedForeign arguments receiver
    rw [target] at selected
    exact selected_pinned_code (by simpa only [accounts] using pinned) selected

end Rollup.EVM
