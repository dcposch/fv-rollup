import proofs.ScalarGetterEquivalence
import proofs.SequencerGetterEquivalence
import proofs.MappingGetterEquivalence
import proofs.SelectorTable

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Rollup.EVM

/-- Scalar getter equivalence includes source selector correspondence. -/
theorem scalar_getter_correct {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (getter : ScalarGetter) (code : I.code = runtimeBytecode)
    (length : 4 ≤ I.calldata.size) (bounded : I.calldata.size < UInt256.size)
    (selector : solcSelectorWord I = scalarSelector getter)
    (maps : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  apply scalar_getter_equivalence_for getter code length bounded selector _ maps
  cases getter with
  | stateRoot => exact source_selector_dispatch I ⟨4, by decide⟩ length selector
  | batchNumber => exact source_selector_dispatch I ⟨5, by decide⟩ length selector
  | backing => exact source_selector_dispatch I ⟨6, by decide⟩ length selector

/-- Sequencer getter equivalence includes source selector correspondence. -/
theorem sequencer_getter_correct {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (code : I.code = runtimeBytecode)
    (length : 4 ≤ I.calldata.size) (bounded : I.calldata.size < UInt256.size)
    (selector : solcSelectorWord I = ⟨0x5c1bba38⟩)
    (maps : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I :=
  sequencer_getter_equivalence_for code length bounded selector
    (source_selector_dispatch I ⟨3, by decide⟩ length selector) maps

/-- Credit getter equivalence includes source selectors and malformed arguments. -/
theorem mapping_getter_correct {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (getter : MappingGetter) (code : I.code = runtimeBytecode)
    (length : 4 ≤ I.calldata.size) (bounded : I.calldata.size < UInt256.size)
    (selector : solcSelectorWord I = mappingSelector getter)
    (maps : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  apply mapping_getter_equivalence_for getter code bounded selector _ maps
  cases getter with
  | pendingDeposits => exact source_selector_dispatch I ⟨7, by decide⟩ length selector
  | pendingWithdrawals => exact source_selector_dispatch I ⟨8, by decide⟩ length selector

/-- All six getters match the source for static and writable calls. -/
theorem getters_correct {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (code : I.code = runtimeBytecode)
    (length : 4 ≤ I.calldata.size) (bounded : I.calldata.size < UInt256.size)
    (getter : solcSelectorWord I ∈ ([⟨0x5c1bba38⟩, ⟨0x9588eca2⟩, ⟨0xba873065⟩,
      ⟨0xc9503fe2⟩, ⟨0xeb3349b9⟩, ⟨0xf3f43703⟩] : List UInt256))
    (maps : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at getter
  rcases getter with seq | root | number | backing | pending | claims
  · exact sequencer_getter_correct code length bounded seq maps
  · exact scalar_getter_correct .stateRoot code length bounded root maps
  · exact scalar_getter_correct .batchNumber code length bounded number maps
  · exact scalar_getter_correct .backing code length bounded backing maps
  · exact mapping_getter_correct .pendingDeposits code length bounded pending maps
  · exact mapping_getter_correct .pendingWithdrawals code length bounded claims maps

end Rollup.EVM
