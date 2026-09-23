import proofs.CreationPrefix

open Ethereum Ethereum.EVM Reasoning.Theory

namespace Rollup.EVM

/-- A creation transfer to its own sender leaves every other balance unchanged. -/
theorem sendEthCreate_same_other_balance (accounts : AccountMap) (sender self : Address)
    (value : UInt256) (foreign : self ≠ sender) :
    ethLedger (sendEthCreate sender sender value true accounts) self = ethLedger accounts self := by
  cases found : accounts.find? sender with
  | none => simp [sendEthCreate, found]
  | some account =>
    rw [sendEthCreate_true_find?_some sender sender value accounts account found]
    simp [ethLedger, Batteries.RBMap.findD, accountMap_find?_insert_ne _ _ _ _ foreign]

/-- A funded creation transfer cannot debit the rollup, even at a colliding address. -/
theorem sendEthCreate_protected_balance (accounts : AccountMap) (receiver sender self : Address)
    (value : UInt256) (foreign : self ≠ sender)
    (funds : value.toNat ≤ ethLedger accounts sender) (world : worldEth accounts < wordLimit) :
    ethLedger accounts self ≤ ethLedger (sendEthCreate receiver sender value true accounts) self := by
  by_cases same : receiver = sender
  · subst receiver
    rw [sendEthCreate_same_other_balance accounts sender self value foreign]
  · exact sendEthCreate_other_balance accounts receiver sender self value true same foreign funds world

/-- The initialization entry keeps the payment reservation for every creation address. -/
theorem creation_transfer_safe (call : CreationCall) {self : Address}
    (keys : AccessScope) (payment : Payment) (foreign : self ≠ call.sender)
    (funds : call.value.toNat ≤ ethLedger call.accounts call.sender)
    (initial : LockedWorld self call.accounts)
    (safe : Safe (inFlightProjection (accountView self call.accounts) self keys payment)) :
    Safe (inFlightProjection call.entryState self keys payment) := by
  have frame : CodeStorageFrame self call.accounts call.entryState.accountMap :=
    sendEthCreate_static_state call.address call.sender call.value true call.accounts self
  have balance := sendEthCreate_protected_balance call.accounts call.address call.sender self call.value
    foreign funds (LockedWorld.bounded initial)
  have projected := CodeStorageFrame.project
    (before := accountView self call.accounts) (after := call.entryState) frame keys
  have model : inFlightProjection call.entryState self keys payment =
      { inFlightProjection (accountView self call.accounts) self keys payment with
        eth := (project call.entryState self keys).eth } := by
    unfold inFlightProjection
    rw [projected]
  apply callback_preserves_safe safe
  rw [model]
  apply callback_of_surplus
  · simpa only [inFlightProjection, project_ethLedger, accountView] using balance
  · rw [project_ethLedger]
    exact (call.entryState.accountMap.findD self default).balance.val.isLt

/-- Both fresh and colliding initialization prefixes preserve the payment reservation. -/
theorem creation_prefix_safe (call : CreationCall) {self : Address} {current : Ethereum.State}
    (keys : AccessScope) (payment : Payment) (foreign : self ≠ call.sender)
    (nonce : (call.accounts.findD call.sender default).nonce ≠ ⟨0⟩)
    (funds : call.value.toNat ≤ ethLedger call.accounts call.sender)
    (initial : LockedWorld self call.accounts)
    (safe : Safe (inFlightProjection (accountView self call.accounts) self keys payment))
    (trace : InstructionPrefix (D_J call.environment.code 0) call.entryState current) :
    Safe (inFlightProjection current self keys payment) := by
  cases collision : call.collision with
  | false => exact (creation_fresh_prefix_safe call keys payment foreign nonce collision funds initial safe trace).2
  | true =>
    rw [creation_collision_prefix call collision trace]
    exact creation_transfer_safe call keys payment foreign funds initial safe

end Rollup.EVM
