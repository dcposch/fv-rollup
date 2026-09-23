import proofs.StaticClassification
import proofs.RuntimeEquivalence
import proofs.AcceptedCallClassification
import proofs.GetterAcceptedBinding

open Solm Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Rollup.EVM

/-- Successful runtime execution matches the source in static and writable calls. -/
theorem runtime_success_equivalence_for {cA gh bl σ σ_solm σ₀ A I} {g : UInt256}
    {cA' σ' gas substate output} (code : I.code = runtimeBytecode)
    (bounded : I.calldata.size < UInt256.size) (maps : accountMapEquiv σ σ_solm)
    (success : Ξ cA gh bl σ σ₀ g A I = .ok (.success (cA', σ', gas, substate) output)) :
    runtimeEquivalenceFor config contract cA gh bl σ σ_solm σ₀ g A I := by
  cases writable : I.perm with
  | true => exact runtime_equivalence_for code writable bounded maps
  | false =>
    exact getters_correct code (runtime_success_length code success) bounded
      (runtime_static_success_getter code writable bounded success) maps

/-- Successful runtime execution supplies its call label in either permission mode. -/
theorem runtime_success_call_bound {cA gh bl σ σ₀ A I} {g : UInt256}
    {cA' σ' gas substate output} (code : I.code = runtimeBytecode)
    (bounded : I.calldata.size < UInt256.size)
    (success : Ξ cA gh bl σ σ₀ g A I = .ok (.success (cA', σ', gas, substate) output)) :
    ∃ locals call, CallBound (initState cA gh bl σ σ₀ (.ofUInt256 g) A I) locals call := by
  cases writable : I.perm with
  | true => exact runtime_accepted_call_bound code writable bounded success
  | false =>
    obtain ⟨locals, getter, bound⟩ := getter_accepted_call_bound code bounded
      (runtime_static_success_getter code writable bounded success) success
    exact ⟨locals, _, bound⟩

end Rollup.EVM
