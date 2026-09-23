import semantics.ChildCreation
import proofs.CreationOpcode
import proofs.CreationTransfer

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- Creation guards preserve the reservation through fresh or colliding initialization. -/
theorem creation_site_prefix_safe (site : CreationSite) (before : Ethereum.State) (cost : Nat)
    (allowed : site.guard before) {self : Address} {current : Ethereum.State}
    (keys : AccessScope) (payment : Payment)
    (foreign : self ≠ before.executionEnv.codeOwner)
    (bounded : (before.accountMap.findD before.executionEnv.codeOwner default).nonce.toNat < 2 ^ 64 - 1)
    (initial : LockedWorld self before.accountMap)
    (safe : Safe (inFlightProjection before self keys payment))
    (trace : InstructionPrefix (D_J (site.call before cost allowed).environment.code 0)
      (site.call before cost allowed).entryState current) :
    Safe (inFlightProjection current self keys payment) := by
  obtain ⟨next, nextSafe⟩ := creation_site_reservation site before cost allowed keys payment initial safe
  exact creation_prefix_safe (site.call before cost allowed) keys payment foreign
    (creation_site_nonce site before cost allowed bounded)
    (creation_site_funded site before cost allowed) next nextSafe trace

/-- An actual creation entry and every prefix of its frame keep the payment backed. -/
theorem child_creation_prefix_safe {before child current : Ethereum.State}
    {jumps : Array UInt256} {self : Address} (keys : AccessScope) (payment : Payment)
    (entered : ChildCreationEntry jumps before child)
    (foreign : self ≠ before.executionEnv.codeOwner)
    (initial : LockedWorld self before.accountMap)
    (safe : Safe (inFlightProjection before self keys payment))
    (trace : InstructionPrefix (D_J child.executionEnv.code 0) child current) :
    Safe (inFlightProjection current self keys payment) := by
  cases entered with
  | @entered op arg checked cost site instruction precheck arguments bounded allowed =>
    have accounts := precheck_accounts precheck
    have environment := Z_executionEnv_eq precheck
    have checkedForeign : self ≠ checked.executionEnv.codeOwner := by
      simpa only [environment] using foreign
    have checkedInitial : LockedWorld self checked.accountMap := by rwa [accounts]
    have checkedSafe : Safe (inFlightProjection
        { checked with executionEnv.depth := before.executionEnv.depth } self keys payment) := by
      simpa only [inFlightProjection, project_boundary, accounts] using safe
    exact creation_site_prefix_safe site _ cost allowed keys payment checkedForeign bounded
      checkedInitial checkedSafe trace

end Rollup.EVM
