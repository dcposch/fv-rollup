import proofs.DepositEquivalence

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Rollup.EVM

/-- Deposit outcomes agree for all calldata and equivalent account maps.
    Both dispatchers must select deposit. Selector hash correspondence is separate. -/
theorem deposit_equivalence_for {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (code : I.code = runtimeBytecode) (writable : I.perm = true)
    (bounded : I.calldata.size < UInt256.size)
    (selector : solcSelectorWord I = ⟨0xf340fa01⟩)
    (dispatch : dispatchMsg contract I.calldata = some contract.transitions[0]!)
    (maps : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have reject (rejected : RDrev runtimeBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I))
      (decoded : decodeCalldata ["owner"] [abiAddress] I.calldata = none) :
      runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
    have equivalent := rejected.reEquivDecodingFailed (σ_solm := σ_solm) (cfg := config)
      code dispatch decoded
    simpa [Sat256.ofUInt256, Sat256.toUInt256] using equivalent
  by_cases four : 4 ≤ I.calldata.size
  · obtain ⟨_, _, dispatched⟩ := runtime_deposit_dispatch (cA := cA) (gh := gh) (bl := bl)
      (σ := σ_evm) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) code four bounded selector
    by_cases length : 36 ≤ I.calldata.size
    · by_cases signedBound : I.calldata.size < 2 ^ 255 + 4
      · by_cases canonical : (calldataWord I.calldata 4).toNat < _root_.EVM.addressModulus
        · exact deposit_decoded_equivalence code writable bounded selector dispatch
            length signedBound canonical maps
        · exact reject (runtime_address_bad_word _ _ length signedBound bounded canonical
            (by evm_ov) dispatched) (decodeCalldata_address_none_noncanon length signedBound canonical)
      · exact reject (runtime_address_bad_length _ _ (by evm_ov)
          (solcDecodeLenCheckHuge_4_32 (by omega) bounded) dispatched)
          (decodeCalldata_address_none_huge (by omega))
    · exact reject (runtime_address_bad_length _ _ (by evm_ov)
        (solcDecodeLenCheckShort_4_32 four (by omega) bounded) dispatched)
        (decodeCalldata_address_none_short four (by omega))
  · apply reject (runtime_short_calldata code (by omega))
    have short : I.calldata.toList.length < 4 := by
      rw [byteArray_toList_eq, Array.length_toList]
      exact Nat.lt_of_not_ge four
    simp only [decodeCalldata, if_pos short]

end Rollup.EVM
