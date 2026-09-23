import proofs.StaticMutationEntries
import proofs.RuntimeGetters

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Rollup.EVM

/-- Every successful static runtime call is a getter. -/
theorem runtime_static_success_getter {cA gh bl σ σ₀ A I} {g : UInt256}
    {cA' σ' gas substate output} (code : I.code = runtimeBytecode)
    (readonly : I.perm = false) (bounded : I.calldata.size < UInt256.size)
    (success : Ξ cA gh bl σ σ₀ g A I = .ok (.success (cA', σ', gas, substate) output)) :
    solcSelectorWord I ∈ ([⟨0x5c1bba38⟩, ⟨0x9588eca2⟩, ⟨0xba873065⟩,
      ⟨0xc9503fe2⟩, ⟨0xeb3349b9⟩, ⟨0xf3f43703⟩] : List UInt256) := by
  have known := runtime_success_selector (g := Sat256.ofUInt256 g) code bounded success
  simp only [runtimeSelectors, List.mem_cons, List.not_mem_nil, or_false] at known
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rcases known with seq | batch | root | number | withdrawal | backing | pending | deposit | claims
  · exact Or.inl seq
  · exact False.elim (batch_static_no_success code readonly bounded batch success)
  · exact Or.inr (Or.inl root)
  · exact Or.inr (Or.inr (Or.inl number))
  · exact False.elim (withdrawal_static_no_success code readonly bounded withdrawal success)
  · exact Or.inr (Or.inr (Or.inr (Or.inl backing)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl pending))))
  · exact False.elim (deposit_static_no_success code readonly bounded deposit success)
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr claims))))

/-- Successful static calls have zero call value and preserve all accounts. -/
theorem runtime_static_preserves_accounts {cA gh bl σ σ₀ A I} {g : UInt256}
    {cA' σ' gas substate output} (code : I.code = runtimeBytecode)
    (readonly : I.perm = false) (bounded : I.calldata.size < UInt256.size)
    (success : Ξ cA gh bl σ σ₀ g A I = .ok (.success (cA', σ', gas, substate) output)) :
    I.weiValue = ⟨0⟩ ∧ cA' = cA ∧ σ' = σ :=
  getter_xi_preserves_accounts (g := Sat256.ofUInt256 g) code bounded
    (runtime_static_success_getter code readonly bounded success) success

end Rollup.EVM
