import semantics.ExecutionPrefix
import proofs.CallbackBalances
import proofs.WithdrawalCallbackModel
import proofs.Transitions

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- Continuing instruction prefixes preserve the execution environment. -/
theorem continuing_prefix_environment {jumps : Array UInt256} {start current : Ethereum.State}
    (trace : ContinuingPrefix jumps start current) : current.executionEnv = start.executionEnv := by
  induction trace with
  | initial => rfl
  | @next before after earlier step ih =>
    have environment := Xstep_env_unchanged before after jumps none step
    change { after.executionEnv with depth := before.executionEnv.depth } = start.executionEnv
    rw [← environment]
    exact ih

/-- Each callback prefix preserves protected storage, code, lock, and ETH bounds. -/
theorem continuing_callback_prefix {self : Address} {jumps : Array UInt256}
    {start current : Ethereum.State}
    (foreign : self ≠ start.executionEnv.codeOwner) (initial : LockedWorld self start.accountMap)
    (trace : ContinuingPrefix jumps start current) :
    EthFrame self start.accountMap current.accountMap ∧
      CodeStorageFrame self start.accountMap current.accountMap ∧ LockedWorld self current.accountMap := by
  induction trace with
  | initial => exact ⟨EthFrame.refl _ _, CodeStorageFrame.refl _ _, initial⟩
  | @next before after earlier step ih =>
    have environment := continuing_prefix_environment earlier
    have different : self ≠ before.executionEnv.codeOwner := by rwa [environment]
    have frames := foreign_xstep_balances (foreign_step_balances self before.executionEnv.depth)
      rfl different ih.2.2 step
    exact ⟨ih.1.trans frames.1, ih.2.1.trans frames.2, ih.2.2.next frames.2 frames.1⟩

/-- The same frame guarantees hold at a halting instruction or a continuing prefix. -/
theorem callback_instruction_prefix {self : Address} {jumps : Array UInt256}
    {start current : Ethereum.State}
    (foreign : self ≠ start.executionEnv.codeOwner) (initial : LockedWorld self start.accountMap)
    (trace : InstructionPrefix jumps start current) :
    EthFrame self start.accountMap current.accountMap ∧
      CodeStorageFrame self start.accountMap current.accountMap ∧ LockedWorld self current.accountMap := by
  cases trace with
  | current earlier => exact continuing_callback_prefix foreign initial earlier
  | @afterStep before after ret earlier step =>
    have ih := continuing_callback_prefix foreign initial earlier
    have environment := continuing_prefix_environment earlier
    have different : self ≠ before.executionEnv.codeOwner := by rwa [environment]
    have frames := foreign_xstep_balances (foreign_step_balances self before.executionEnv.depth)
      rfl different ih.2.2 step
    exact ⟨ih.1.trans frames.1, ih.2.1.trans frames.2, ih.2.2.next frames.2 frames.1⟩

/-- Fixed protected storage and surplus ETH preserve the reserved-payment model. -/
theorem inFlight_frame_callback {self : Address} {before after : Ethereum.State}
    (keys : AccessScope) (payment : Payment)
    (frame : CodeStorageFrame self before.accountMap after.accountMap)
    (balances : EthFrame self before.accountMap after.accountMap) :
    Callback (inFlightProjection before self keys payment) (inFlightProjection after self keys payment) := by
  have projected := CodeStorageFrame.project (before := before) (after := after) frame keys
  have updated : inFlightProjection after self keys payment =
      { inFlightProjection before self keys payment with eth := (project after self keys).eth } := by
    unfold inFlightProjection
    rw [projected]
  rw [updated]
  apply callback_of_surplus
  · simpa only [inFlightProjection, project_ethLedger] using balances.2
  · rw [project_ethLedger]
    exact (after.accountMap.findD self default).balance.val.isLt

/-- The payment reservation remains safe at every instruction boundary in a receiver frame. -/
theorem callback_prefix_safe {self : Address} {jumps : Array UInt256}
    {start current : Ethereum.State} (keys : AccessScope) (payment : Payment)
    (foreign : self ≠ start.executionEnv.codeOwner) (initial : LockedWorld self start.accountMap)
    (safe : Safe (inFlightProjection start self keys payment))
    (trace : InstructionPrefix jumps start current) : Safe (inFlightProjection current self keys payment) := by
  have frames := callback_instruction_prefix foreign initial trace
  exact callback_preserves_safe safe (inFlight_frame_callback keys payment frames.2.1 frames.1)

end Rollup.EVM
