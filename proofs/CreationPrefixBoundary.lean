import proofs.ChildPrefixBoundary
import proofs.ActiveCreationEntry

open Ethereum Ethereum.EVM

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

namespace Rollup.EVM

/-- Creation enters invalid collision code or a foreign frame with the boundary preserved. -/
theorem child_creation_entry_boundary {before child : Ethereum.State} {jumps : Array UInt256}
    {self : Address} {keys : AccessScope}
    (entered : ChildCreationEntry jumps before child) (foreign : self ≠ before.executionEnv.codeOwner)
    (ready : BoundaryReady self before.accountMap keys)
    (safe : Safe (boundaryModel self before.accountMap keys)) :
    (child.executionEnv.code = ⟨#[0xfe]⟩ ∧ child.machineState.pc = ⟨0⟩) ∨
      (self ≠ child.executionEnv.codeOwner ∧ BoundaryRefines self keys before.accountMap child.accountMap) := by
  cases entered with
  | @entered op arg checked cost site instruction precheck arguments bounded allowed =>
    have accounts := precheck_accounts precheck
    have environment := Z_executionEnv_eq precheck
    have checkedForeign : self ≠ checked.executionEnv.codeOwner := by simpa only [environment] using foreign
    have checkedReady : BoundaryReady self checked.accountMap keys :=
      Eq.mpr (congrArg (fun world => BoundaryReady self world keys) accounts) ready
    have checkedSafe : Safe (boundaryModel self checked.accountMap keys) :=
      Eq.mpr (congrArg (fun world => Safe (boundaryModel self world keys)) accounts) safe
    let parent := { checked with executionEnv.depth := before.executionEnv.depth }
    let call := site.call parent cost allowed
    cases collision : call.collision with
    | true =>
      apply Or.inl
      refine ⟨?_, rfl⟩
      change (if call.collision then (⟨#[0xfe]⟩ : ByteArray) else call.initCode) = _
      rw [collision]
      rfl
    | false =>
      have nonceEffect := boundary_nonce_refines self checked.executionEnv.codeOwner checked.accountMap keys
        checkedReady checkedSafe
      have nonce := creation_site_nonce site parent cost allowed bounded
      have funds := creation_site_funded site parent cost allowed
      have different := creation_fresh_not_sender call nonce collision
      have transfer := boundary_creation_transfer_refines self call.sender call.address call.accounts call.value keys
        nonceEffect.1 nonceEffect.2.1 checkedForeign different funds
      refine Or.inr ⟨creation_fresh_foreign call (BoundaryReady.pinned nonceEffect.1) collision, ?_⟩
      have combined := boundary_refines_trans nonceEffect transfer
      change BoundaryRefines self keys before.accountMap call.initialAccounts
      exact Eq.mp (congrArg (fun world => BoundaryRefines self keys world call.initialAccounts) accounts) combined

end Rollup.EVM
