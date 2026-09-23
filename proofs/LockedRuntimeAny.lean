import proofs.RuntimeAnyDispatch
import proofs.RuntimeAddressAnyDecode
import proofs.RuntimeWithdrawalAnyDecode
import proofs.RuntimeBatchAnyDecode
import proofs.LockedRuntime

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Rollup.EVM

private theorem mapping_any {I : ExecutionEnv} {g : Sat256} {s0 : Ethereum.State}
    {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : Nat}
    (getter : MappingGetter)
    (reached : RD runtimeBytecode I g s0 (mappingEntry getter) [mappingSelector getter]
      solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k C) :
    RDrev runtimeBytecode g s0 ∨ (I.weiValue = ⟨0⟩ ∧ ∃ output, RDret runtimeBytecode g s0 (cA, σ) output) := by
  by_cases value : I.weiValue = ⟨0⟩
  · obtain ⟨_, _, decoder⟩ := mapping_getter_decoder getter _ (by simp) value reached
    rcases runtime_address_decode_any (mappingEntry getter + ⟨26⟩) [⟨249⟩, mappingSelector getter]
        (mapping_body_destination getter) (by simp) decoder with
      rejected | ⟨_, _, _, decoded⟩
    · exact .inl rejected
    · exact .inr ⟨value, _, mapping_getter_return getter _ _ (by simp) decoded⟩
  · exact .inl (mapping_getter_nonpayable getter _ (by simp) value reached)

/-- Every locked entry rejects or returns without changing accounts, for all calldata. -/
theorem locked_runtime_any_entry {I : ExecutionEnv} {g : Sat256} {s0 : Ethereum.State}
    {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : Nat}
    (entry : RuntimeEntry) (locked : solcSlotWord σ I ⟨6⟩ ≠ ⟨0⟩)
    (reached : RD runtimeBytecode I g s0 (runtimeEntryPC entry) [runtimeEntrySelector entry]
      solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k C) :
    RDrev runtimeBytecode g s0 ∨ (I.weiValue = ⟨0⟩ ∧ ∃ output, RDret runtimeBytecode g s0 (cA, σ) output) := by
  cases entry with
  | sequencer =>
    by_cases value : I.weiValue = ⟨0⟩
    · exact .inr ⟨value, _, sequencer_getter_return _ (by simp) value reached⟩
    · exact .inl (sequencer_getter_nonpayable _ (by simp) value reached)
  | stateRoot =>
    by_cases value : I.weiValue = ⟨0⟩
    · exact .inr ⟨value, _, scalar_getter_return .stateRoot _ (by simp) value reached⟩
    · exact .inl (scalar_getter_nonpayable .stateRoot _ (by simp) value reached)
  | batchNumber =>
    by_cases value : I.weiValue = ⟨0⟩
    · exact .inr ⟨value, _, scalar_getter_return .batchNumber _ (by simp) value reached⟩
    · exact .inl (scalar_getter_nonpayable .batchNumber _ (by simp) value reached)
  | backing =>
    by_cases value : I.weiValue = ⟨0⟩
    · exact .inr ⟨value, _, scalar_getter_return .backing _ (by simp) value reached⟩
    · exact .inl (scalar_getter_nonpayable .backing _ (by simp) value reached)
  | pendingDeposits => exact mapping_any .pendingDeposits reached
  | pendingWithdrawals => exact mapping_any .pendingWithdrawals reached
  | deposit =>
    have decoder := runtime_run reached with [jumpdest, push2 ⟨226⟩, push2 ⟨393⟩,
      calldatasize, push1 ⟨4⟩, push2 ⟨1331⟩,
      jump (jumpScan_valid runtimeBytecode 1331 1350 (by decide +kernel))]
    rcases runtime_address_decode_any ⟨393⟩ [⟨226⟩, ⟨0xf340fa01⟩]
        (jumpScan_valid runtimeBytecode 393 410 (by decide +kernel)) (by decide) decoder with
      rejected | ⟨_, _, _, decoded⟩
    · exact .inl rejected
    · have entered := runtime_run decoded with [jumpdest, push2 ⟨1045⟩,
        jump (jumpScan_valid runtimeBytecode 1045 1060 (by decide +kernel))]
      exact .inl (deposit_bytecode_locked _ (by simp) locked entered)
  | withdrawal =>
    by_cases value : I.weiValue = ⟨0⟩
    · obtain ⟨_, _, decoder⟩ := mutation_decoder .withdrawal _ (by simp) value reached
      rcases withdrawal_decode_any ⟨310⟩ [⟨226⟩, ⟨0xbb3ef682⟩]
          (jumpScan_valid runtimeBytecode 310 340 (by decide +kernel)) (by decide) decoder with
        rejected | ⟨_, _, _, decoded⟩
      · exact .inl rejected
      · have entered := runtime_run decoded with [jumpdest, push2 ⟨843⟩,
          jump (jumpScan_valid runtimeBytecode 843 880 (by decide +kernel))]
        exact .inl (withdrawal_bytecode_locked _ (by simp) locked entered)
    · exact .inl (mutation_nonpayable .withdrawal _ (by simp) value reached)
  | batch =>
    by_cases value : I.weiValue = ⟨0⟩
    · obtain ⟨_, _, decoder⟩ := mutation_decoder .batch _ (by simp) value reached
      rcases batch_decode_any ⟨221⟩ [⟨226⟩, ⟨0x88af9950⟩]
          (jumpScan_valid runtimeBytecode 221 240 (by decide +kernel)) (by decide) decoder with
        rejected | ⟨_, _, _, _, decoded⟩
      · exact .inl rejected
      · dsimp only [batchDecodedStack] at decoded
        have entered := runtime_run decoded with [jumpdest, push2 ⟨441⟩,
          jump (jumpScan_valid runtimeBytecode 441 470 (by decide +kernel))]
        exact .inl (batch_bytecode_locked _ (by simp) locked entered)
    · exact .inl (mutation_nonpayable .batch _ (by simp) value reached)

/-- Accepted locked execution preserves every account without a calldata-size premise. -/
theorem locked_runtime_xi_preserves_accounts_any {cA gh bl σ σ₀ A I} {g : Sat256}
    {cA' σ' gas substate output} (code : I.code = runtimeBytecode)
    (locked : solcSlotWord σ I ⟨6⟩ ≠ ⟨0⟩)
    (success : Ξ cA gh bl σ σ₀ g.toUInt256 A I = .ok (.success (cA', σ', gas, substate) output)) :
    I.weiValue = ⟨0⟩ ∧ cA' = cA ∧ σ' = σ := by
  have notRejected (rejected : RDrev runtimeBytecode g (initState cA gh bl σ σ₀ g A I)) : False := by
    rcases rejected.xiResult code with failed | ⟨gas', data, actual⟩
    · rw [success] at failed
      cases failed
    · rw [success] at actual
      cases actual
  rcases runtime_dispatch_any (cA := cA) (gh := gh) (bl := bl) (σ := σ)
      (σ₀ := σ₀) (A := A) (g := g) code with rejected | ⟨entry, _, _, reached⟩
  · exact (notRejected rejected).elim
  · rcases locked_runtime_any_entry entry locked reached with rejected | ⟨value, bytes, returned⟩
    · exact (notRejected rejected).elim
    · rcases returned with failed | ⟨finalState, result, accounts⟩
      · have impossible := Xi_error_of_X (g := g.toUInt256) (by
          rw [← code] at failed
          simpa [initState, Sat256.ofUInt256, Sat256.toUInt256] using failed)
        rw [success] at impossible
        cases impossible
      · have actual := Xi_success_of_X (g := g.toUInt256) (by
          rw [← code] at result
          simpa [initState, Sat256.ofUInt256, Sat256.toUInt256] using result)
        rw [success] at actual
        cases actual
        exact ⟨value, congrArg Prod.fst accounts, congrArg Prod.snd accounts⟩

end Rollup.EVM
