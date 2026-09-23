import proofs.CallbackPrefix
import proofs.WorldCreationTransfers

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- A nested call's funded transfer preserves the locked rollup and its reservation. -/
theorem callback_transfer_safe (before after : Ethereum.State)
    (self sender receiver : Address) (value : UInt256) (keys : AccessScope) (payment : Payment)
    (safeSender : self ≠ sender ∨ value = ⟨0⟩) (initial : LockedWorld self before.accountMap)
    (safe : Safe (inFlightProjection before self keys payment))
    (funds : value.toNat ≤ ethLedger before.accountMap sender)
    (transferred : after.accountMap = sendEth receiver sender value true before.accountMap) :
    LockedWorld self after.accountMap ∧ Safe (inFlightProjection after self keys payment) := by
  have frame : CodeStorageFrame self before.accountMap after.accountMap := by
    rw [transferred]
    exact sendEth_accountStaticStateEq receiver sender value true before.accountMap self
  have balances : EthFrame self before.accountMap after.accountMap := by
    rw [transferred]
    exact ⟨(sendEth_world _ _ _ _ _ funds (LockedWorld.bounded initial)).le,
      sendEth_protected_balance _ _ _ _ _ _ safeSender funds (LockedWorld.bounded initial)⟩
  exact ⟨initial.next frame balances,
    callback_preserves_safe safe (inFlight_frame_callback keys payment frame balances)⟩

/-- A funded creation transfer preserves the locked rollup and its reservation. -/
theorem callback_creation_transfer_safe (before after : Ethereum.State)
    (self sender receiver : Address) (value : UInt256) (keys : AccessScope) (payment : Payment)
    (foreign : self ≠ sender) (different : receiver ≠ sender)
    (initial : LockedWorld self before.accountMap)
    (safe : Safe (inFlightProjection before self keys payment))
    (funds : value.toNat ≤ ethLedger before.accountMap sender)
    (transferred : after.accountMap = sendEthCreate receiver sender value true before.accountMap) :
    LockedWorld self after.accountMap ∧ Safe (inFlightProjection after self keys payment) := by
  have frame : CodeStorageFrame self before.accountMap after.accountMap := by
    rw [transferred]
    exact sendEthCreate_static_state receiver sender value true before.accountMap self
  have balances : EthFrame self before.accountMap after.accountMap := by
    rw [transferred]
    exact ⟨(sendEthCreate_world_ne _ _ _ _ _ different funds (LockedWorld.bounded initial)).le,
      sendEthCreate_other_balance _ _ _ _ _ _ different foreign funds (LockedWorld.bounded initial)⟩
  exact ⟨initial.next frame balances,
    callback_preserves_safe safe (inFlight_frame_callback keys payment frame balances)⟩

end Rollup.EVM
