import proofs.SelectorTable
import proofs.RuntimeUnknownSelector

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Rollup.EVM

private theorem transition_index (t : TransitionDecl) (member : t ∈ contract.transitions) :
    ∃ index : Fin 9, t = contract.transitions[index.val]! := by
  change t ∈ [contract.transitions[0]!, contract.transitions[1]!, contract.transitions[2]!,
    contract.transitions[3]!, contract.transitions[4]!, contract.transitions[5]!,
    contract.transitions[6]!, contract.transitions[7]!, contract.transitions[8]!] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with h | h | h | h | h | h | h | h | h
  · exact ⟨⟨0, by decide⟩, h⟩
  · exact ⟨⟨1, by decide⟩, h⟩
  · exact ⟨⟨2, by decide⟩, h⟩
  · exact ⟨⟨3, by decide⟩, h⟩
  · exact ⟨⟨4, by decide⟩, h⟩
  · exact ⟨⟨5, by decide⟩, h⟩
  · exact ⟨⟨6, by decide⟩, h⟩
  · exact ⟨⟨7, by decide⟩, h⟩
  · exact ⟨⟨8, by decide⟩, h⟩

/-- Source dispatch rejects calldata shorter than a selector. -/
theorem source_short_calldata (I : ExecutionEnv) (short : I.calldata.size < 4) :
    dispatchMsg contract I.calldata = none := by
  apply dispatchMsg_none_of_all_ne rfl rfl
  intro t member
  obtain ⟨index, rfl⟩ := transition_index t member
  rw [source_selector_bytes]
  by_contra matched
  have bytes := byteArray_size_eq_of_beq (Bool.eq_true_of_not_eq_false matched)
  have size : (sourceSelectorBytes index).size = 4 := by fin_cases index <;> rfl
  rw [size, ByteArray.size_extract] at bytes
  omega

/-- Source dispatch rejects every selector absent from the bytecode table. -/
theorem source_unknown_selector (I : ExecutionEnv)
    (unknown : solcSelectorWord I ∉ runtimeSelectors) :
    dispatchMsg contract I.calldata = none := by
  by_cases length : 4 ≤ I.calldata.size
  · apply dispatchMsg_none_of_all_ne rfl rfl
    intro t member
    obtain ⟨index, rfl⟩ := transition_index t member
    rw [source_selector_bytes]
    by_contra mismatch
    have matched := Bool.eq_true_of_not_eq_false mismatch
    have comparison := source_selector_comparison I index length
    rw [matched] at comparison
    have same : sourceSelectorWord index = solcSelectorWord I := uInt256_eq_one_eq comparison
    have known : sourceSelectorWord index ∈ runtimeSelectors := by
      fin_cases index <;> decide +kernel
    exact unknown (same ▸ known)
  · exact source_short_calldata I (by omega)

/-- Short calldata has equivalent EVM and source rejection. -/
theorem short_calldata_correct {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (code : I.code = runtimeBytecode) (short : I.calldata.size < 4) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have rejected := runtime_short_calldata (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) code short
  exact rejected.reEquivNoDispatch code (source_short_calldata I short)

/-- Unknown selectors have equivalent EVM and source rejection. -/
theorem unknown_selector_correct {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (code : I.code = runtimeBytecode) (bounded : I.calldata.size < UInt256.size)
    (unknown : solcSelectorWord I ∉ runtimeSelectors) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have rejected := runtime_unknown_selector (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) code bounded unknown
  exact rejected.reEquivNoDispatch code (source_unknown_selector I unknown)

end Rollup.EVM
