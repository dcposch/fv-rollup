import proofs.WithdrawalPrefix
import proofs.ActiveCallback

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- The actual withdrawal transfer remains safe throughout the receiver's active call tree. -/
theorem withdrawal_callback_active_safe (before entry current : Ethereum.State)
    (owner : Address) (value : UInt256) (keys : AccessScope)
    (code : OwnCode before) (world : WorldBounded before)
    (ready : StorageReady before before.executionEnv.codeOwner keys)
    (safe : Safe (project before before.executionEnv.codeOwner keys))
    (enabled : WithdrawalEnabled (project before before.executionEnv.codeOwner keys) owner value.toNat)
    (entered : entry.accountMap = sendEth owner before.executionEnv.codeOwner value true
      (withdrawalLockedState before).accountMap)
    (foreign : before.executionEnv.codeOwner ≠ entry.executionEnv.codeOwner)
    (trace : ActivePrefix entry current) :
    Safe (inFlightProjection current before.executionEnv.codeOwner keys
      ⟨owner, value.toNat, (project before before.executionEnv.codeOwner keys).eth⟩) := by
  obtain ⟨locked, entrySafe⟩ := withdrawal_transfer_safe before owner value keys code world ready safe enabled
  apply callback_active_prefix_safe keys _ foreign _ _ trace
  · rwa [entered]
  · simpa only [inFlightProjection, project_boundary, entered, accountView] using entrySafe

/-- ETH plus the reserved payment backs credit at every active callback depth. -/
theorem withdrawal_callback_active_custody (before entry current : Ethereum.State)
    (owner : Address) (value : UInt256) (keys : AccessScope)
    (code : OwnCode before) (world : WorldBounded before)
    (ready : StorageReady before before.executionEnv.codeOwner keys)
    (safe : Safe (project before before.executionEnv.codeOwner keys))
    (enabled : WithdrawalEnabled (project before before.executionEnv.codeOwner keys) owner value.toNat)
    (entered : entry.accountMap = sendEth owner before.executionEnv.codeOwner value true
      (withdrawalLockedState before).accountMap)
    (foreign : before.executionEnv.codeOwner ≠ entry.executionEnv.codeOwner)
    (trace : ActivePrefix entry current) :
    liabilities (project current before.executionEnv.codeOwner keys) ≤
      (project current before.executionEnv.codeOwner keys).eth + value.toNat :=
  (withdrawal_callback_active_safe before entry current owner value keys code world ready safe enabled
    entered foreign trace).1

end Rollup.EVM
