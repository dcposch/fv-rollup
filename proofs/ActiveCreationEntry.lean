import proofs.ChildCreation
import proofs.ActiveFailure

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- An actual creation enters a safe foreign frame or a collision stub that cannot advance. -/
theorem child_creation_active_cases {before child : Ethereum.State} {jumps : Array UInt256}
    {self : Address} (keys : AccessScope) (payment : Payment)
    (entered : ChildCreationEntry jumps before child) (foreign : self ≠ before.executionEnv.codeOwner)
    (initial : LockedWorld self before.accountMap) (safe : Safe (inFlightProjection before self keys payment)) :
    Safe (inFlightProjection child self keys payment) ∧
      ((∀ current, ActivePrefix child current → current = child) ∨
        (self ≠ child.executionEnv.codeOwner ∧ LockedWorld self child.accountMap)) := by
  cases entered with
  | @entered op arg checked cost site instruction precheck arguments bounded allowed =>
    have accounts := precheck_accounts precheck
    have environment := Z_executionEnv_eq precheck
    have checkedForeign : self ≠ checked.executionEnv.codeOwner := by simpa only [environment] using foreign
    have checkedInitial : LockedWorld self checked.accountMap := by rwa [accounts]
    have checkedSafe : Safe (inFlightProjection
        { checked with executionEnv.depth := before.executionEnv.depth } self keys payment) := by
      simpa only [inFlightProjection, project_boundary, accounts] using safe
    obtain ⟨next, nextSafe⟩ := creation_site_reservation site _ cost allowed keys payment checkedInitial checkedSafe
    let call := site.call { checked with executionEnv.depth := before.executionEnv.depth } cost allowed
    have funds := creation_site_funded site _ cost allowed
    have nonce := creation_site_nonce site _ cost allowed bounded
    refine ⟨creation_transfer_safe call keys payment checkedForeign funds next nextSafe, ?_⟩
    cases collision : call.collision with
    | true =>
      exact .inl (fun current trace => creation_collision_active_prefix call collision trace)
    | false =>
      have entry := creation_fresh_prefix_safe call keys payment checkedForeign nonce collision funds
        next nextSafe (.current .initial)
      exact .inr ⟨creation_fresh_foreign call (LockedWorld.pinned next) collision, entry.1⟩

end Rollup.EVM
