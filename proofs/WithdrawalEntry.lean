import proofs.RuntimeMutationDispatch
import proofs.RuntimeWithdrawalDecode
import proofs.RuntimeMutationLocks

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Rollup.EVM

/-- A withdrawal rejects or reaches its body with decoded arguments. -/
theorem withdrawal_entry_classification {cA gh bl σ σ₀ A I} {g : Sat256}
    (code : I.code = runtimeBytecode) (bounded : I.calldata.size < UInt256.size)
    (selector : solcSelectorWord I = ⟨0xbb3ef682⟩) :
    RDrev runtimeBytecode g (initState cA gh bl σ σ₀ g A I) ∨
      (I.weiValue = ⟨0⟩ ∧ 68 ≤ I.calldata.size ∧ I.calldata.size < 2 ^ 255 + 4 ∧
       (calldataWord I.calldata 4).toNat < _root_.EVM.addressModulus ∧
       ∃ k C, RD runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨843⟩
         [calldataWord I.calldata 36, calldataWord I.calldata 4, ⟨226⟩, ⟨0xbb3ef682⟩]
         solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) := by
  by_cases four : 4 ≤ I.calldata.size
  · obtain ⟨_, _, dispatched⟩ := mutation_dispatch (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (g := g) .withdrawal code four bounded selector
    by_cases value : I.weiValue = ⟨0⟩
    · obtain ⟨_, _, decoder⟩ := mutation_decoder .withdrawal [⟨0xbb3ef682⟩] (by decide) value dispatched
      by_cases length : 68 ≤ I.calldata.size
      · by_cases signedBound : I.calldata.size < 2 ^ 255 + 4
        · by_cases canonical : (calldataWord I.calldata 4).toNat < _root_.EVM.addressModulus
          · obtain ⟨_, _, decoded⟩ := withdrawal_decode ⟨310⟩ [⟨226⟩, ⟨0xbb3ef682⟩]
              length signedBound bounded canonical
              (jumpScan_valid runtimeBytecode 310 340 (by decide +kernel)) (by decide) decoder
            exact Or.inr ⟨value, length, signedBound, canonical, _, _, runtime_run decoded with
              [jumpdest, push2 ⟨843⟩, jump (jumpScan_valid runtimeBytecode 843 880 (by decide +kernel))]⟩
          · exact Or.inl (withdrawal_decode_bad_owner _ _ length signedBound bounded canonical
              (by decide) decoder)
        · exact Or.inl (withdrawal_decode_bad_length _ _ (by decide)
            (solcDecodeLenCheckHuge_4_64 (by omega) bounded) decoder)
      · exact Or.inl (withdrawal_decode_bad_length _ _ (by decide)
          (solcDecodeLenCheckShort_4_64 four (by omega) bounded) decoder)
    · exact Or.inl (mutation_nonpayable .withdrawal _ (by decide) value dispatched)
  · exact Or.inl (runtime_short_calldata code (by omega))

/-- Every withdrawal selector rejects while the lock is set, for all calldata. -/
theorem withdrawal_locked_reject {cA gh bl σ σ₀ A I} {g : Sat256}
    (code : I.code = runtimeBytecode) (bounded : I.calldata.size < UInt256.size)
    (selector : solcSelectorWord I = ⟨0xbb3ef682⟩)
    (locked : solcSlotWord σ I ⟨6⟩ ≠ ⟨0⟩) :
    RDrev runtimeBytecode g (initState cA gh bl σ σ₀ g A I) := by
  rcases withdrawal_entry_classification (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (g := g) code bounded selector with
    rejected | ⟨_, _, _, _, _, _, reached⟩
  · exact rejected
  · exact withdrawal_bytecode_locked _ (by simp) locked reached

/-- An accepted withdrawal passed its value, decoder, and lock checks. -/
theorem withdrawal_xi_entry_checks {cA gh bl σ σ₀ A I} {g : Sat256}
    {cA' σ' gas substate output} (code : I.code = runtimeBytecode)
    (bounded : I.calldata.size < UInt256.size)
    (selector : solcSelectorWord I = ⟨0xbb3ef682⟩)
    (success : Ξ cA gh bl σ σ₀ g.toUInt256 A I = .ok (.success (cA', σ', gas, substate) output)) :
    I.weiValue = ⟨0⟩ ∧ 68 ≤ I.calldata.size ∧ I.calldata.size < 2 ^ 255 + 4 ∧
      (calldataWord I.calldata 4).toNat < _root_.EVM.addressModulus ∧ solcSlotWord σ I ⟨6⟩ = ⟨0⟩ := by
  have notRejected (rejected : RDrev runtimeBytecode g (initState cA gh bl σ σ₀ g A I)) : False := by
    rcases rejected.xiResult code with failed | ⟨gas', data, actual⟩
    · rw [success] at failed
      cases failed
    · rw [success] at actual
      cases actual
  rcases withdrawal_entry_classification (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (g := g) code bounded selector with
    rejected | ⟨value, length, signedBound, canonical, _⟩
  · exact False.elim (notRejected rejected)
  · refine ⟨value, length, signedBound, canonical, ?_⟩
    by_contra locked
    exact notRejected (withdrawal_locked_reject code bounded selector locked)

end Rollup.EVM
