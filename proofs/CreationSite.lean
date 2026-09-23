import semantics.CreationSite
import proofs.WorldNonce
import proofs.CreationPrefix

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- A decoded creation site identifies CREATE or CREATE2. -/
theorem creation_opcode_kind {before : Ethereum.State} {op : Operation} {site : CreationSite}
    (decoded : CreationSite.decode before op = some site) : op = .CREATE ∨ op = .CREATE2 := by
  cases op <;> rename_i command <;> cases command <;> simp_all [CreationSite.decode]

/-- The actual creation call uses the nonce-incremented account map. -/
theorem creation_site_accounts (site : CreationSite) (before : Ethereum.State) (cost : Nat)
    (allowed : site.guard before) :
    (site.call before cost allowed).accounts = incrementNonce before.accountMap before.executionEnv.codeOwner := rfl

/-- The creation funds check supplies the endowment after the nonce update. -/
theorem creation_site_funded (site : CreationSite) (before : Ethereum.State) (cost : Nat)
    (allowed : site.guard before) :
    (site.call before cost allowed).value.toNat ≤
      ethLedger (site.call before cost allowed).accounts (site.call before cost allowed).sender := by
  change site.value.toNat ≤ ethLedger (incrementNonce before.accountMap before.executionEnv.codeOwner)
    before.executionEnv.codeOwner
  rw [incrementNonce_ethLedger, ethLedger_lookup]
  have funds := allowed.1
  change site.value.toNat ≤ (Option.option (⟨0⟩ : UInt256) (fun (x : Account) => x.balance)
    (before.accountMap.find? before.executionEnv.codeOwner)).toNat at funds
  cases found : before.accountMap.find? before.executionEnv.codeOwner <;>
    simpa [found, Option.option, UInt256.toNat] using funds

/-- The nonce-limit check makes the creation caller's incremented nonce nonzero. -/
theorem creation_site_nonce (site : CreationSite) (before : Ethereum.State) (cost : Nat)
    (allowed : site.guard before)
    (bounded : (before.accountMap.findD before.executionEnv.codeOwner default).nonce.toNat < 2 ^ 64 - 1) :
    ((site.call before cost allowed).accounts.findD (site.call before cost allowed).sender default).nonce ≠ ⟨0⟩ :=
  incrementNonce_nonzero before.accountMap before.executionEnv.codeOwner bounded

/-- The nonce update keeps the locked rollup and its payment reservation. -/
theorem creation_site_reservation (site : CreationSite) (before : Ethereum.State) (cost : Nat)
    (allowed : site.guard before) {self : Address} (keys : AccessScope) (payment : Payment)
    (initial : LockedWorld self before.accountMap)
    (safe : Safe (inFlightProjection before self keys payment)) :
    LockedWorld self (site.call before cost allowed).accounts ∧
      Safe (inFlightProjection (accountView self (site.call before cost allowed).accounts) self keys payment) := by
  have frame := incrementNonce_storage before.accountMap before.executionEnv.codeOwner self
  have balances : EthFrame self before.accountMap (site.call before cost allowed).accounts := by
    simp only [creation_site_accounts, EthFrame, worldEth, incrementNonce_ethLedger]
    exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  exact ⟨incrementNonce_lockedWorld initial,
    callback_preserves_safe safe (inFlight_frame_callback keys payment frame balances)⟩

/-- Opcode guards establish the inputs needed for fresh initialization-prefix safety. -/
theorem creation_site_fresh_prefix (site : CreationSite) (before : Ethereum.State) (cost : Nat)
    (allowed : site.guard before) {self : Address} {current : Ethereum.State}
    (keys : AccessScope) (payment : Payment)
    (foreign : self ≠ before.executionEnv.codeOwner)
    (bounded : (before.accountMap.findD before.executionEnv.codeOwner default).nonce.toNat < 2 ^ 64 - 1)
    (fresh : (site.call before cost allowed).collision = false)
    (initial : LockedWorld self before.accountMap)
    (safe : Safe (inFlightProjection before self keys payment))
    (trace : InstructionPrefix (D_J (site.call before cost allowed).environment.code 0)
      (site.call before cost allowed).entryState current) :
    LockedWorld self current.accountMap ∧ Safe (inFlightProjection current self keys payment) := by
  obtain ⟨next, nextSafe⟩ := creation_site_reservation site before cost allowed keys payment initial safe
  exact creation_fresh_prefix_safe (site.call before cost allowed) keys payment foreign
    (creation_site_nonce site before cost allowed bounded) fresh
    (creation_site_funded site before cost allowed) next nextSafe trace

end Rollup.EVM
