import invariants.Callbacks
import proofs.ActiveCallEntry
import proofs.ActiveCreationEntry

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- Nested calls and creations preserve the payment reservation at every active prefix. -/
theorem callback_active_prefix_safe {self : Address} {start current : Ethereum.State}
    (keys : AccessScope) (payment : Payment) (foreign : self ≠ start.executionEnv.codeOwner)
    (initial : LockedWorld self start.accountMap)
    (safe : Safe (inFlightProjection start self keys payment)) (trace : ActivePrefix start current) :
    Safe (inFlightProjection current self keys payment) := by
  revert foreign initial safe
  induction trace with
  | within earlier =>
    intro foreign initial safe
    exact callback_prefix_safe keys payment foreign initial safe earlier
  | @call start before child current earlier entered later ih =>
    intro foreign initial safe
    have environment := continuing_prefix_environment earlier
    have beforeForeign : self ≠ before.executionEnv.codeOwner := by rwa [environment]
    have frames := continuing_callback_prefix foreign initial earlier
    have beforeSafe := callback_prefix_safe keys payment foreign initial safe (.current earlier)
    obtain ⟨childLocked, childSafe⟩ := child_call_entry_safe keys payment entered beforeForeign frames.2.2 beforeSafe
    by_cases different : self ≠ child.executionEnv.codeOwner
    · exact ih different childLocked childSafe
    · have owner : child.executionEnv.codeOwner = self := (not_ne_iff.mp different).symm
      have accounts := child_call_locked_active_accounts entered beforeForeign
        (LockedWorld.pinned frames.2.2) childLocked owner later
      simpa only [inFlightProjection, project_boundary, accounts] using childSafe
  | @creation start before child current earlier entered later ih =>
    intro foreign initial safe
    have environment := continuing_prefix_environment earlier
    have beforeForeign : self ≠ before.executionEnv.codeOwner := by rwa [environment]
    have frames := continuing_callback_prefix foreign initial earlier
    have beforeSafe := callback_prefix_safe keys payment foreign initial safe (.current earlier)
    obtain ⟨childSafe, cases⟩ := child_creation_active_cases keys payment entered beforeForeign frames.2.2 beforeSafe
    rcases cases with stopped | ⟨childForeign, childLocked⟩
    · rw [stopped current later]
      exact childSafe
    · exact ih childForeign childLocked childSafe

/-- Full active-prefix callback safety, including calls into the locked rollup. -/
theorem callback_active_prefix_correct : CallbackActivePrefixCorrect := by
  intro self start current keys payment foreign pinned locked bounded safe trace
  apply callback_active_prefix_safe keys payment foreign _ safe trace
  exact ⟨pinned, by simpa only [readWord_default] using locked,
    (worldBounded_iff_worldEth start).mp bounded⟩

end Rollup.EVM
