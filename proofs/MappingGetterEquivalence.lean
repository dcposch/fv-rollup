import proofs.RuntimeMappingDispatch
import proofs.GetterValues
import Reasoning.Dispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Rollup.EVM

def mappingModelGetter (getter : MappingGetter) (owner : AccountAddress) : Getter :=
  match getter with
  | .pendingDeposits => .pendingDeposits owner
  | .pendingWithdrawals => .pendingWithdrawals owner

theorem mapping_getter_value_init {cA gh bl σ σ₀ A I} {g : Sat256}
    (getter : MappingGetter) (owner : AccountAddress) :
    getterValue (initState cA gh bl σ σ₀ g A I) (mappingModelGetter getter owner) =
      .int (solcSlotWord σ I (solcMappingSlot (mappingSlot getter) (UInt256.ofNat owner.val))).toNat := by
  cases getter <;>
    simp only [getterValue, mappingModelGetter, mappingSlot, keySlot, mapSlot,
      keyValueToWord_address, solcMappingSlot] <;> rfl

/-- Decoded credit getters have equivalent EVM and source outcomes. -/
theorem mapping_getter_decoded_equivalence {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (getter : MappingGetter) (code : I.code = runtimeBytecode)
    (bounded : I.calldata.size < UInt256.size)
    (selector : solcSelectorWord I = mappingSelector getter)
    (dispatch : dispatchMsg contract I.calldata = some (entryTransition (.read
      (mappingModelGetter getter (AccountAddress.ofNat (calldataWord I.calldata 4).toNat)))))
    (length : 36 ≤ I.calldata.size) (signedBound : I.calldata.size < 2 ^ 255 + 4)
    (canonical : (calldataWord I.calldata 4).toNat < _root_.EVM.addressModulus)
    (maps : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let owner := AccountAddress.ofNat (calldataWord I.calldata 4).toNat
  have decodedWord : calldataWord I.calldata 4 = UInt256.ofNat owner.val := by
    have same := keyValueToWord_address_of_canonical _ canonical
    rw [keyValueToWord_address] at same
    exact same.symm
  have decoded : decodeCalldataWithMode config.abiDecodeMode
      ((entryTransition (.read (mappingModelGetter getter owner))).params.map Param.name)
      (transitionSignature (entryTransition (.read (mappingModelGetter getter owner)))).paramTypes
      I.calldata = some (getterLocals (mappingModelGetter getter owner)) := by
    cases getter <;> exact decodeCalldata_address_ok length signedBound canonical
  obtain ⟨_, _, reached⟩ := mapping_getter_dispatch (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) getter code (by omega) bounded selector
  by_cases value : I.weiValue = ⟨0⟩
  · obtain ⟨_, _, decoder⟩ := mapping_getter_decoder getter [mappingSelector getter]
      (by simp) value reached
    obtain ⟨_, _, parsed⟩ := runtime_address_decode (mappingEntry getter + ⟨26⟩)
      [⟨249⟩, mappingSelector getter] length signedBound bounded canonical
      (mapping_body_destination getter) (by simp) decoder
    have returned := mapping_getter_return getter _ [mappingSelector getter] (by simp) parsed
    have source := (getter_source_exact (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
      (mappingModelGetter getter owner) value).1
    have word : solcSlotWord σ_solm I (solcMappingSlot (mappingSlot getter) (calldataWord I.calldata 4)) =
        solcSlotWord σ_evm I (solcMappingSlot (mappingSlot getter) (calldataWord I.calldata 4)) :=
      (accountMapEquiv_storage_findD maps I.codeOwner _ ⟨0⟩).symm
    have values : some [getterValue (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (mappingModelGetter getter owner)] = some [.int
          (solcSlotWord σ_evm I (solcMappingSlot (mappingSlot getter) (calldataWord I.calldata 4))).toNat] := by
      rw [mapping_getter_value_init, ← decodedWord, word]
    have encoding : returnEquiv
        (UInt256.toByteArray (solcSlotWord σ_evm I (solcMappingSlot (mappingSlot getter) (calldataWord I.calldata 4))))
        (some [.int (solcSlotWord σ_evm I (solcMappingSlot (mappingSlot getter) (calldataWord I.calldata 4))).toNat])
        (entryTransition (.read (mappingModelGetter getter owner))).returnType := by
      cases getter <;> exact returnEquiv_of_encode (uint256ReturnEncoding _)
    exact returned.reEquivExecutionTransport code dispatch decoded source values maps encoding
  · have rejected := mapping_getter_nonpayable getter [mappingSelector getter] (by simp) value reached
    have source : ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (getterLocals (mappingModelGetter getter owner))
        (entryTransition (.read (mappingModelGetter getter owner))).body .reverted := by
      cases getter <;> exact .execBlockRevert (.consRevert (.requireFalse (evalCallvalueEq_false value)))
    exact rejected.reEquivExecutionRevert code dispatch decoded source

/-- Credit getters agree for valid and malformed arguments. -/
theorem mapping_getter_equivalence_for {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (getter : MappingGetter) (code : I.code = runtimeBytecode)
    (bounded : I.calldata.size < UInt256.size)
    (selector : solcSelectorWord I = mappingSelector getter)
    (dispatch : dispatchMsg contract I.calldata = some (entryTransition (.read
      (mappingModelGetter getter (AccountAddress.ofNat (calldataWord I.calldata 4).toNat)))))
    (maps : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have reject (invalid : ¬ (36 ≤ I.calldata.size ∧ I.calldata.size < 2 ^ 255 + 4 ∧
        (calldataWord I.calldata 4).toNat < _root_.EVM.addressModulus))
      (decoded : decodeCalldata ["owner"] [abiAddress] I.calldata = none) :
      runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
    have rejected : RDrev runtimeBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) := by
      rcases mapping_getter_classification (cA := cA) (gh := gh) (bl := bl)
          (σ := σ_evm) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g)
          getter code bounded selector with rejected | ⟨_, length, signedBound, canonical, _⟩
      · exact rejected
      · exact False.elim (invalid ⟨length, signedBound, canonical⟩)
    have decodeNone : decodeCalldataWithMode config.abiDecodeMode
        ((entryTransition (.read (mappingModelGetter getter
          (AccountAddress.ofNat (calldataWord I.calldata 4).toNat)))).params.map Param.name)
        (transitionSignature (entryTransition (.read (mappingModelGetter getter
          (AccountAddress.ofNat (calldataWord I.calldata 4).toNat))))).paramTypes I.calldata = none := by
      cases getter <;> exact decoded
    exact rejected.reEquivDecodingFailed (σ_solm := σ_solm) (cfg := config) code dispatch decodeNone
  by_cases four : 4 ≤ I.calldata.size
  · by_cases length : 36 ≤ I.calldata.size
    · by_cases signedBound : I.calldata.size < 2 ^ 255 + 4
      · by_cases canonical : (calldataWord I.calldata 4).toNat < _root_.EVM.addressModulus
        · exact mapping_getter_decoded_equivalence getter code bounded selector dispatch
            length signedBound canonical maps
        · exact reject (fun h => canonical h.2.2)
            (decodeCalldata_address_none_noncanon length signedBound canonical)
      · exact reject (fun h => signedBound h.2.1) (decodeCalldata_address_none_huge (by omega))
    · exact reject (fun h => length h.1) (decodeCalldata_address_none_short four (by omega))
  · apply reject (fun h => four (by omega))
    have short : I.calldata.toList.length < 4 := by
      rw [byteArray_toList_eq, Array.length_toList]
      exact Nat.lt_of_not_ge four
    simp only [decodeCalldata, if_pos short]

end Rollup.EVM
