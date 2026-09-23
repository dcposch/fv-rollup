import proofs.GetterCallBinding
import proofs.AcceptedCallBinding

open Solm Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Rollup.EVM

/-- Every accepted writable runtime call has a label bound to its actual calldata. -/
theorem runtime_accepted_call_bound {cA gh bl σ σ₀ A I} {g : UInt256}
    {cA' σ' gas substate output}
    (code : I.code = runtimeBytecode) (writable : I.perm = true)
    (bounded : I.calldata.size < UInt256.size)
    (success : Ξ cA gh bl σ σ₀ g A I = .ok (.success (cA', σ', gas, substate) output)) :
    ∃ locals call, CallBound (initState cA gh bl σ σ₀ (.ofUInt256 g) A I) locals call := by
  have length := runtime_success_length code success
  have known := runtime_success_selector (g := Sat256.ofUInt256 g) code bounded success
  simp only [runtimeSelectors, List.mem_cons, List.not_mem_nil, or_false] at known
  rcases known with seq | batch | root | number | withdrawal | backing | pending | deposit | claims
  · exact ⟨_, _, sequencer_getter_call_bound _ length seq⟩
  · exact ⟨_, _, batch_accepted_call_bound code writable bounded batch success⟩
  · exact ⟨_, _, scalar_getter_call_bound _ .stateRoot length root⟩
  · exact ⟨_, _, scalar_getter_call_bound _ .batchNumber length number⟩
  · exact ⟨_, _, withdrawal_accepted_call_bound code writable bounded withdrawal success⟩
  · exact ⟨_, _, scalar_getter_call_bound _ .backing length backing⟩
  · obtain ⟨_, size, signedBound, canonical, _⟩ :=
      mapping_getter_xi_success (g := Sat256.ofUInt256 g) .pendingDeposits code bounded pending success
    exact ⟨_, _, mapping_getter_call_bound _ .pendingDeposits size signedBound canonical pending⟩
  · exact ⟨_, _, deposit_accepted_call_bound code writable bounded deposit success⟩
  · obtain ⟨_, size, signedBound, canonical, _⟩ :=
      mapping_getter_xi_success (g := Sat256.ofUInt256 g) .pendingWithdrawals code bounded claims success
    exact ⟨_, _, mapping_getter_call_bound _ .pendingWithdrawals size signedBound canonical claims⟩

end Rollup.EVM
