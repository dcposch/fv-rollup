import proofs.RuntimeMutationDispatch
import proofs.BatchDecodeClassification
import proofs.RuntimeMutationLocks

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Rollup.EVM

/-- A batch rejects or reaches its body with seven decoded words. -/
theorem batch_entry_classification {cA gh bl σ σ₀ A I} {g : Sat256}
    (code : I.code = runtimeBytecode) (bounded : I.calldata.size < UInt256.size)
    (selector : solcSelectorWord I = ⟨0x88af9950⟩) :
    RDrev runtimeBytecode g (initState cA gh bl σ σ₀ g A I) ∨
      (I.weiValue = ⟨0⟩ ∧ 228 ≤ I.calldata.size ∧ I.calldata.size < 2 ^ 255 + 4 ∧
       (calldataWord I.calldata 100).toNat < _root_.EVM.addressModulus ∧
       (calldataWord I.calldata 164).toNat < _root_.EVM.addressModulus ∧
       ∃ k C, RD runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨441⟩
         (batchDecodedStack I [⟨226⟩, ⟨0x88af9950⟩])
         solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) := by
  by_cases four : 4 ≤ I.calldata.size
  · obtain ⟨_, _, dispatched⟩ := mutation_dispatch (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (g := g) .batch code four bounded selector
    by_cases value : I.weiValue = ⟨0⟩
    · obtain ⟨_, _, decoder⟩ := mutation_decoder .batch [⟨0x88af9950⟩] (by decide) value dispatched
      rcases batch_decode_classification ⟨221⟩ [⟨226⟩, ⟨0x88af9950⟩] four bounded
          (jumpScan_valid runtimeBytecode 221 240 (by decide +kernel)) (by decide) decoder with
        rejected | ⟨length, signedBound, first, second, _, _, decoded⟩
      · exact Or.inl rejected
      · dsimp only [batchDecodedStack] at decoded
        exact Or.inr ⟨value, length, signedBound, first, second, _, _, runtime_run decoded with
          [jumpdest, push2 ⟨441⟩, jump (jumpScan_valid runtimeBytecode 441 470 (by decide +kernel))]⟩
    · exact Or.inl (mutation_nonpayable .batch _ (by decide) value dispatched)
  · exact Or.inl (runtime_short_calldata code (by omega))

/-- Every batch selector rejects while the lock is set, for all calldata. -/
theorem batch_locked_reject {cA gh bl σ σ₀ A I} {g : Sat256}
    (code : I.code = runtimeBytecode) (bounded : I.calldata.size < UInt256.size)
    (selector : solcSelectorWord I = ⟨0x88af9950⟩)
    (locked : solcSlotWord σ I ⟨6⟩ ≠ ⟨0⟩) :
    RDrev runtimeBytecode g (initState cA gh bl σ σ₀ g A I) := by
  rcases batch_entry_classification (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (g := g) code bounded selector with
    rejected | ⟨_, _, _, _, _, _, _, reached⟩
  · exact rejected
  · exact batch_bytecode_locked _ (by simp [batchDecodedStack]) locked reached

/-- An accepted batch passed its value, decoder, and lock checks. -/
theorem batch_xi_entry_checks {cA gh bl σ σ₀ A I} {g : Sat256}
    {cA' σ' gas substate output} (code : I.code = runtimeBytecode)
    (bounded : I.calldata.size < UInt256.size)
    (selector : solcSelectorWord I = ⟨0x88af9950⟩)
    (success : Ξ cA gh bl σ σ₀ g.toUInt256 A I = .ok (.success (cA', σ', gas, substate) output)) :
    I.weiValue = ⟨0⟩ ∧ 228 ≤ I.calldata.size ∧ I.calldata.size < 2 ^ 255 + 4 ∧
      (calldataWord I.calldata 100).toNat < _root_.EVM.addressModulus ∧
      (calldataWord I.calldata 164).toNat < _root_.EVM.addressModulus ∧ solcSlotWord σ I ⟨6⟩ = ⟨0⟩ := by
  have notRejected (rejected : RDrev runtimeBytecode g (initState cA gh bl σ σ₀ g A I)) : False := by
    rcases rejected.xiResult code with failed | ⟨gas', data, actual⟩
    · rw [success] at failed
      cases failed
    · rw [success] at actual
      cases actual
  rcases batch_entry_classification (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (g := g) code bounded selector with
    rejected | ⟨value, length, signedBound, first, second, _⟩
  · exact False.elim (notRejected rejected)
  · refine ⟨value, length, signedBound, first, second, ?_⟩
    by_contra locked
    exact notRejected (batch_locked_reject code bounded selector locked)

end Rollup.EVM
