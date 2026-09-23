import proofs.GetterCallBinding

open Solm Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Rollup.EVM

/-- Accepted getters supply their decoded labels in static and writable calls. -/
theorem getter_accepted_call_bound {cA gh bl σ σ₀ A I} {g : UInt256}
    {cA' σ' gas substate output} (code : I.code = runtimeBytecode)
    (bounded : I.calldata.size < UInt256.size)
    (selected : solcSelectorWord I ∈ ([⟨0x5c1bba38⟩, ⟨0x9588eca2⟩, ⟨0xba873065⟩,
      ⟨0xc9503fe2⟩, ⟨0xeb3349b9⟩, ⟨0xf3f43703⟩] : List UInt256))
    (success : Ξ cA gh bl σ σ₀ g A I = .ok (.success (cA', σ', gas, substate) output)) :
    ∃ locals getter, CallBound (initState cA gh bl σ σ₀ (.ofUInt256 g) A I) locals
      ⟨I.source, I.weiValue.toNat, .read getter⟩ := by
  have length := runtime_success_length code success
  simp only [List.mem_cons, List.not_mem_nil, or_false] at selected
  rcases selected with seq | root | number | backing | pending | claims
  · exact ⟨_, _, sequencer_getter_call_bound _ length seq⟩
  · exact ⟨_, _, scalar_getter_call_bound _ .stateRoot length root⟩
  · exact ⟨_, _, scalar_getter_call_bound _ .batchNumber length number⟩
  · exact ⟨_, _, scalar_getter_call_bound _ .backing length backing⟩
  · obtain ⟨_, size, signedBound, canonical, _⟩ :=
      mapping_getter_xi_success (g := Sat256.ofUInt256 g) .pendingDeposits code bounded pending success
    exact ⟨_, _, mapping_getter_call_bound _ .pendingDeposits size signedBound canonical pending⟩
  · obtain ⟨_, size, signedBound, canonical, _⟩ :=
      mapping_getter_xi_success (g := Sat256.ofUInt256 g) .pendingWithdrawals code bounded claims success
    exact ⟨_, _, mapping_getter_call_bound _ .pendingWithdrawals size signedBound canonical claims⟩

end Rollup.EVM
