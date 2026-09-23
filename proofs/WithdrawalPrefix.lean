import proofs.CallbackPrefix
import proofs.Boundary

open Ethereum Ethereum.EVM Solm Reasoning.Theory

namespace Rollup.EVM

/-- The actual transfer establishes a safe reservation and keeps the rollup locked. -/
theorem withdrawal_transfer_safe (before : Ethereum.State) (owner : Address) (value : UInt256)
    (keys : AccessScope) (code : OwnCode before) (world : WorldBounded before)
    (ready : StorageReady before before.executionEnv.codeOwner keys)
    (safe : Safe (project before before.executionEnv.codeOwner keys))
    (enabled : WithdrawalEnabled (project before before.executionEnv.codeOwner keys) owner value.toNat) :
    let self := before.executionEnv.codeOwner
    let accounts := sendEth owner self value true (withdrawalLockedState before).accountMap
    let payment : Payment := ⟨owner, value.toNat, (project before self keys).eth⟩
    LockedWorld self accounts ∧ Safe (inFlightProjection (accountView self accounts) self keys payment) := by
  let self := before.executionEnv.codeOwner
  let locked := withdrawalLockedState before
  let accounts := sendEth owner self value true locked.accountMap
  let entry := accountView self accounts
  let payment : Payment := ⟨owner, value.toNat, (project before self keys).eth⟩
  have initial := withdrawal_locked_world code world
  have funds : value.toNat ≤ ethLedger locked.accountMap self := by
    simpa only [locked, withdrawalLockedState, source_store_ethLedger, project_ethLedger] using enabled.2.2.2
  have worldBound := LockedWorld.bounded initial
  have frame : CodeStorageFrame self locked.accountMap accounts :=
    sendEth_accountStaticStateEq owner self value true locked.accountMap self
  have lockedAfter : LockedWorld self accounts := by
    refine ⟨frame.2.2.symm.trans (LockedWorld.pinned initial), ?_, ?_⟩
    · rw [← frame.1]
      exact LockedWorld.locked initial
    · change worldEth (sendEth owner self value true locked.accountMap) < wordLimit
      rwa [sendEth_world _ _ _ _ _ funds worldBound]
  have projected := CodeStorageFrame.project (before := locked) (after := entry) frame keys
  have lockedModel := withdrawal_lock_projection before keys code ready
  have model : inFlightProjection entry self keys payment =
      { beginWithdrawal (project before self keys) owner value.toNat with eth := (project entry self keys).eth } := by
    unfold inFlightProjection
    rw [projected]
    change { { project (withdrawalLockedState before) self keys with eth := (project entry self keys).eth }
      with payment := some payment } = _
    rw [lockedModel]
    rfl
  have lower : (project before self keys).eth - value.toNat ≤ (project entry self keys).eth := by
    have amount := sendEth_sender_lower_bound locked.accountMap owner self value true funds worldBound
    simpa only [project_ethLedger, entry, accountView, accounts, locked, withdrawalLockedState,
      source_store_ethLedger] using amount
  have callback : Callback (beginWithdrawal (project before self keys) owner value.toNat)
      (inFlightProjection entry self keys payment) := by
    rw [model]
    apply callback_of_surplus _ _ lower
    rw [project_ethLedger]
    exact (accounts.findD self default).balance.val.isLt
  exact ⟨lockedAfter, callback_preserves_safe (begin_safe safe enabled) callback⟩

/-- The receiver's instruction prefixes preserve the reservation established by the transfer. -/
theorem withdrawal_callback_prefix_safe (before entry current : Ethereum.State)
    (owner : Address) (value : UInt256) (keys : AccessScope) (jumps : Array UInt256)
    (code : OwnCode before) (world : WorldBounded before)
    (ready : StorageReady before before.executionEnv.codeOwner keys)
    (safe : Safe (project before before.executionEnv.codeOwner keys))
    (enabled : WithdrawalEnabled (project before before.executionEnv.codeOwner keys) owner value.toNat)
    (entered : entry.accountMap = sendEth owner before.executionEnv.codeOwner value true
      (withdrawalLockedState before).accountMap)
    (foreign : before.executionEnv.codeOwner ≠ entry.executionEnv.codeOwner)
    (trace : InstructionPrefix jumps entry current) :
    Safe (inFlightProjection current before.executionEnv.codeOwner keys
      ⟨owner, value.toNat, (project before before.executionEnv.codeOwner keys).eth⟩) := by
  obtain ⟨locked, initialSafe⟩ := withdrawal_transfer_safe before owner value keys code world ready safe enabled
  have currentLocked : LockedWorld before.executionEnv.codeOwner entry.accountMap := by
    rwa [entered]
  have initialModel : inFlightProjection entry before.executionEnv.codeOwner keys
      ⟨owner, value.toNat, (project before before.executionEnv.codeOwner keys).eth⟩ =
      inFlightProjection
        (accountView before.executionEnv.codeOwner
          (sendEth owner before.executionEnv.codeOwner value true (withdrawalLockedState before).accountMap))
        before.executionEnv.codeOwner keys
        ⟨owner, value.toNat, (project before before.executionEnv.codeOwner keys).eth⟩ := by
    simp only [inFlightProjection, project_boundary, entered, accountView]
  apply callback_prefix_safe keys _ foreign currentLocked _ trace
  rwa [initialModel]

/-- Physical credit remains backed by ETH plus the reserved payment at receiver instruction boundaries. -/
theorem withdrawal_callback_prefix_custody (before entry current : Ethereum.State)
    (owner : Address) (value : UInt256) (keys : AccessScope) (jumps : Array UInt256)
    (code : OwnCode before) (world : WorldBounded before)
    (ready : StorageReady before before.executionEnv.codeOwner keys)
    (safe : Safe (project before before.executionEnv.codeOwner keys))
    (enabled : WithdrawalEnabled (project before before.executionEnv.codeOwner keys) owner value.toNat)
    (entered : entry.accountMap = sendEth owner before.executionEnv.codeOwner value true
      (withdrawalLockedState before).accountMap)
    (foreign : before.executionEnv.codeOwner ≠ entry.executionEnv.codeOwner)
    (trace : InstructionPrefix jumps entry current) :
    liabilities (project current before.executionEnv.codeOwner keys) ≤
      (project current before.executionEnv.codeOwner keys).eth + value.toNat :=
  (withdrawal_callback_prefix_safe before entry current owner value keys jumps code world ready safe enabled
    entered foreign trace).1

end Rollup.EVM
