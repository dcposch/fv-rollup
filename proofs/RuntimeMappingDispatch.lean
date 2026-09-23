import proofs.RuntimeMappingGetter

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Rollup.EVM

/-- Each credit selector reaches its getter without changing accounts. -/
theorem mapping_getter_dispatch {cA gh bl σ σ₀ A I} {g : Sat256}
    (getter : MappingGetter) (code : I.code = runtimeBytecode)
    (length : 4 ≤ I.calldata.size) (bounded : I.calldata.size < UInt256.size)
    (selector : solcSelectorWord I = mappingSelector getter) :
    ∃ k C, RD runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) (mappingEntry getter)
      [mappingSelector getter] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, loaded⟩ := runtime_selector (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) code length bounded
  rw [selector] at loaded
  have split := runtime_run loaded with [dup1, push4 ⟨0xbb3ef682⟩, gt, push2 ⟨87⟩,
    jumpiNT (by cases getter <;> decide +kernel)]
  have first := runtime_run split with [dup1, push4 ⟨0xbb3ef682⟩, eq, push2 ⟨284⟩,
    jumpiNT (by cases getter <;> decide +kernel)]
  have second := runtime_run first with [dup1, push4 ⟨0xc9503fe2⟩, eq, push2 ⟨315⟩,
    jumpiNT (by cases getter <;> decide +kernel)]
  cases getter with
  | pendingDeposits =>
    exact ⟨_, _, runtime_run second with [dup1, push4 ⟨0xeb3349b9⟩, eq, push2 ⟨336⟩,
      jumpiT (by decide +kernel) (jumpScan_valid runtimeBytecode 336 440 (by decide +kernel))]⟩
  | pendingWithdrawals =>
    have third := runtime_run second with [dup1, push4 ⟨0xeb3349b9⟩, eq, push2 ⟨336⟩,
      jumpiNT (by decide +kernel)]
    have fourth := runtime_run third with [dup1, push4 ⟨0xf340fa01⟩, eq, push2 ⟨379⟩,
      jumpiNT (by decide +kernel)]
    exact ⟨_, _, runtime_run fourth with [dup1, push4 ⟨0xf3f43703⟩, eq, push2 ⟨398⟩,
      jumpiT (by decide +kernel) (jumpScan_valid runtimeBytecode 398 440 (by decide +kernel))]⟩

/-- Credit getter calls reject or return the stored word. Both paths permit out-of-gas. -/
theorem mapping_getter_classification {cA gh bl σ σ₀ A I} {g : Sat256}
    (getter : MappingGetter) (code : I.code = runtimeBytecode)
    (bounded : I.calldata.size < UInt256.size)
    (selector : solcSelectorWord I = mappingSelector getter) :
    RDrev runtimeBytecode g (initState cA gh bl σ σ₀ g A I) ∨
      (I.weiValue = ⟨0⟩ ∧ 36 ≤ I.calldata.size ∧ I.calldata.size < 2 ^ 255 + 4 ∧
       (calldataWord I.calldata 4).toNat < _root_.EVM.addressModulus ∧
       RDret runtimeBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
         (UInt256.toByteArray (solcSlotWord σ I
           (solcMappingSlot (mappingSlot getter) (calldataWord I.calldata 4))))) := by
  by_cases four : 4 ≤ I.calldata.size
  · obtain ⟨_, _, dispatched⟩ := mapping_getter_dispatch (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (g := g) getter code four bounded selector
    by_cases value : I.weiValue = ⟨0⟩
    · obtain ⟨_, _, decoder⟩ := mapping_getter_decoder getter [mappingSelector getter]
        (by simp) value dispatched
      by_cases length : 36 ≤ I.calldata.size
      · by_cases signedBound : I.calldata.size < 2 ^ 255 + 4
        · by_cases canonical : (calldataWord I.calldata 4).toNat < _root_.EVM.addressModulus
          · obtain ⟨_, _, decoded⟩ := runtime_address_decode (mappingEntry getter + ⟨26⟩)
              [⟨249⟩, mappingSelector getter] length signedBound bounded canonical
              (mapping_body_destination getter) (by simp) decoder
            exact Or.inr ⟨value, length, signedBound, canonical,
              mapping_getter_return getter _ [mappingSelector getter] (by simp) decoded⟩
          · exact Or.inl (runtime_address_bad_word _ _ length signedBound bounded canonical
              (by simp) decoder)
        · exact Or.inl (runtime_address_bad_length _ _ (by simp)
            (solcDecodeLenCheckHuge_4_32 (by omega) bounded) decoder)
      · exact Or.inl (runtime_address_bad_length _ _ (by simp)
          (solcDecodeLenCheckShort_4_32 four (by omega) bounded) decoder)
    · exact Or.inl (mapping_getter_nonpayable getter _ (by simp) value dispatched)
  · exact Or.inl (runtime_short_calldata code (by omega))

/-- Accepted credit getter calls return the exact credit and preserve accounts. -/
theorem mapping_getter_xi_success {cA gh bl σ σ₀ A I} {g : Sat256}
    {cA' σ' gas substate output} (getter : MappingGetter) (code : I.code = runtimeBytecode)
    (bounded : I.calldata.size < UInt256.size)
    (selector : solcSelectorWord I = mappingSelector getter)
    (success : Ξ cA gh bl σ σ₀ g.toUInt256 A I = .ok (.success (cA', σ', gas, substate) output)) :
    I.weiValue = ⟨0⟩ ∧ 36 ≤ I.calldata.size ∧ I.calldata.size < 2 ^ 255 + 4 ∧
      (calldataWord I.calldata 4).toNat < _root_.EVM.addressModulus ∧
      cA' = cA ∧ σ' = σ ∧ output = UInt256.toByteArray
        (solcSlotWord σ I (solcMappingSlot (mappingSlot getter) (calldataWord I.calldata 4))) := by
  have classified := mapping_getter_classification (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) getter code bounded selector
  rcases classified with rejected | ⟨value, length, signedBound, canonical, returned⟩
  · rcases rejected.xiResult code with failed | ⟨gas', data, actual⟩
    · rw [success] at failed
      cases failed
    · rw [success] at actual
      cases actual
  · rcases returned.xiResult code with failed | ⟨gas', substate', actual⟩
    · rw [success] at failed
      cases failed
    · rw [success] at actual
      cases actual
      exact ⟨value, length, signedBound, canonical, rfl, rfl, rfl⟩

end Rollup.EVM
