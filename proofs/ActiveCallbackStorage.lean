import proofs.ActiveCallback
import proofs.ChildEntryStorage

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- Every active callback frame preserves the protected code and storage. -/
theorem callback_active_storage {self : Address} {start current : Ethereum.State}
    (keys : AccessScope) (payment : Payment) (foreign : self ≠ start.executionEnv.codeOwner)
    (initial : LockedWorld self start.accountMap)
    (safe : Safe (inFlightProjection start self keys payment)) (trace : ActivePrefix start current) :
    CodeStorageFrame self start.accountMap current.accountMap := by
  revert foreign initial safe
  induction trace with
  | within earlier =>
    intro foreign initial safe
    exact (callback_instruction_prefix foreign initial earlier).2.1
  | @call start before child current earlier entered later ih =>
    intro foreign initial safe
    have environment := continuing_prefix_environment earlier
    have beforeForeign : self ≠ before.executionEnv.codeOwner := by rwa [environment]
    have frames := continuing_callback_prefix foreign initial earlier
    have beforeSafe := callback_prefix_safe keys payment foreign initial safe (.current earlier)
    obtain ⟨childLocked, childSafe⟩ := child_call_entry_safe keys payment entered beforeForeign frames.2.2 beforeSafe
    have first := frames.2.1.trans (child_call_entry_storage entered self)
    by_cases different : self ≠ child.executionEnv.codeOwner
    · exact first.trans (ih different childLocked childSafe)
    · have owner : child.executionEnv.codeOwner = self := (not_ne_iff.mp different).symm
      have accounts := child_call_locked_active_accounts entered beforeForeign
        (LockedWorld.pinned frames.2.2) childLocked owner later
      rwa [accounts]
  | @creation start before child current earlier entered later ih =>
    intro foreign initial safe
    have environment := continuing_prefix_environment earlier
    have beforeForeign : self ≠ before.executionEnv.codeOwner := by rwa [environment]
    have frames := continuing_callback_prefix foreign initial earlier
    have beforeSafe := callback_prefix_safe keys payment foreign initial safe (.current earlier)
    obtain ⟨childSafe, cases⟩ := child_creation_active_cases keys payment entered beforeForeign frames.2.2 beforeSafe
    have first := frames.2.1.trans (child_creation_entry_storage entered self)
    rcases cases with stopped | ⟨childForeign, childLocked⟩
    · rw [stopped current later]
      exact first
    · exact first.trans (ih childForeign childLocked childSafe)

end Rollup.EVM
