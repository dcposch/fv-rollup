import proofs.TransactionRootEntry
import proofs.RootMessageOrigin

open Ethereum Ethereum.EVM

set_option maxRecDepth 4096

namespace Rollup.EVM

/-- A transaction path binds the root call to its actual funded message. -/
theorem transaction_root_message_origin {event start root self keys}
    (entry : TransactionCodeEntry event start) (path : CoveredRootEntryPath self keys root start)
    (admissible : event.admissible self) (ordinary : self ∉ π)
    (ready : BoundaryReady self event.before keys) (safe : Safe (boundaryModel self event.before keys)) :
    RootMessageOrigin self keys root := by
  have checkpoint := transaction_checkpoint_boundary admissible ready safe
  cases entry with
  | @message recipient code recipientSelected codeSelected =>
    let call := transactionMessage event.before event.baseFee event.header event.genesis event.blocks
      event.transaction event.sender recipient
    have transfer := boundary_transfer_refines self call.sender call.receiver call.accounts call.value keys
      checkpoint.1.1 checkpoint.1.2.1 (Or.inl admissible.1) checkpoint.2.2
    apply root_entry_message_origin path ordinary transfer.1 transfer.2.1
    intro owner
    have receiver : recipient = self := owner
    rw [receiver] at codeSelected
    have pinned := selected_pinned_code (BoundaryReady.pinned checkpoint.1.1) codeSelected
    subst code
    refine ⟨call, rfl, ⟨receiver, ?_, rfl, checkpoint.2.2, ?_⟩, checkpoint.1.1, checkpoint.1.2.1⟩
    · change recipient ≠ event.sender
      rw [receiver]
      exact admissible.1
    · obtain ⟨_, account, _, _, _, _, bounded⟩ := admissible
      exact bounded
  | creation selected =>
    let call := transactionCreation event.before event.baseFee event.header event.genesis event.blocks
      event.transaction event.sender
    cases collision : call.collision with
    | true =>
      have invalid : call.entryState.executionEnv.code = ⟨#[0xfe]⟩ := by
        change (if call.collision then (⟨#[0xfe]⟩ : ByteArray) else call.initCode) = _
        rw [collision]
        rfl
      exact False.elim (root_entry_invalid (covered_root_entry_execution path) invalid rfl)
    | false =>
      have different := creation_fresh_not_sender call checkpoint.2.1 collision
      have transfer := boundary_creation_transfer_refines self call.sender call.address call.accounts call.value keys
        checkpoint.1.1 checkpoint.1.2.1 admissible.1 different checkpoint.2.2
      have foreign := creation_fresh_foreign call (BoundaryReady.pinned checkpoint.1.1) collision
      exact root_entry_message_origin path ordinary transfer.1 transfer.2.1
        (fun same => False.elim (foreign same.symm))

end Rollup.EVM
