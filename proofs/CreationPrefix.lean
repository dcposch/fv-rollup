import proofs.CreationCall
import proofs.CallbackEntry
import proofs.Boundary

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- Fresh initialization code preserves an existing withdrawal reservation. -/
theorem creation_fresh_prefix_safe (call : CreationCall) {self : Address} {current : Ethereum.State}
    (keys : AccessScope) (payment : Payment)
    (foreign : self ≠ call.sender)
    (nonce : (call.accounts.findD call.sender default).nonce ≠ ⟨0⟩)
    (fresh : call.collision = false)
    (funds : call.value.toNat ≤ ethLedger call.accounts call.sender)
    (initial : LockedWorld self call.accounts)
    (safe : Safe (inFlightProjection (accountView self call.accounts) self keys payment))
    (trace : InstructionPrefix (D_J call.environment.code 0) call.entryState current) :
    LockedWorld self current.accountMap ∧ Safe (inFlightProjection current self keys payment) := by
  have different := creation_fresh_not_sender call nonce fresh
  have childForeign := creation_fresh_foreign call (LockedWorld.pinned initial) fresh
  have transferred := callback_creation_transfer_safe (accountView self call.accounts) call.entryState
    self call.sender call.address call.value keys payment foreign different initial safe funds rfl
  exact ⟨(callback_instruction_prefix childForeign transferred.1 trace).2.2,
    callback_prefix_safe keys payment childForeign transferred.1 transferred.2 trace⟩

end Rollup.EVM
