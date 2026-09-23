import proofs.PrefixBoundary
import proofs.ActiveCallEntry

open Ethereum Ethereum.EVM

set_option maxRecDepth 4096

namespace Rollup.EVM

/-- A foreign caller's funded child entry preserves the unlocked rollup boundary. -/
theorem child_call_entry_boundary {before child : Ethereum.State} {jumps : Array UInt256}
    {self : Address} {keys : AccessScope}
    (entered : ChildCallEntry jumps before child) (foreign : self ≠ before.executionEnv.codeOwner)
    (ready : BoundaryReady self before.accountMap keys)
    (safe : Safe (boundaryModel self before.accountMap keys)) :
    BoundaryRefines self keys before.accountMap child.accountMap := by
  cases entered with
  | @entered op arg checked cost site code instruction precheck arguments enabled selected =>
    have accounts := precheck_accounts precheck
    have environment := Z_executionEnv_eq precheck
    have checkedForeign : self ≠ checked.executionEnv.codeOwner := by simpa only [environment] using foreign
    have checkedReady : BoundaryReady self checked.accountMap keys :=
      Eq.mpr (congrArg (fun world => BoundaryReady self world keys) accounts) ready
    have checkedSafe : Safe (boundaryModel self checked.accountMap keys) :=
      Eq.mpr (congrArg (fun world => Safe (boundaryModel self world keys)) accounts) safe
    let parent := callParent { checked with executionEnv.depth := before.executionEnv.depth }
    have source := call_opcode_source arguments
    have senderSafe : self ≠ (site.message parent).sender ∨ site.value = ⟨0⟩ := by
      rcases source with source | zero
      · apply Or.inl
        change self ≠ AccountAddress.ofUInt256 site.source
        intro same
        exact checkedForeign (same.trans source)
      · exact .inr zero
    have transfer := boundary_transfer_refines self (site.message parent).sender
      (site.message parent).receiver parent.accountMap site.value keys checkedReady checkedSafe
      senderSafe (call_site_funded site parent enabled (call_opcode_source arguments))
    simpa only [MessageCall.codeEntry, MessageCall.initialAccounts, CallSite.message, parent,
      callParent, accounts] using transfer

end Rollup.EVM
