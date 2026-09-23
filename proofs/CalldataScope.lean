import semantics.CallScope
import proofs.RuntimeSuccess

open Ethereum Ethereum.EVM Solm Reasoning.Theory Reasoning.Reach

namespace Rollup.EVM

/-- Accepted bytecode supplies both its decoded label and its exact mapping-key set. -/
theorem runtime_success_scoped_binding {cA gh bl σ σ₀ A I} {g : UInt256}
    {cA' σ' gas substate output} (code : I.code = runtimeBytecode)
    (bounded : I.calldata.size < UInt256.size)
    (success : Ξ cA gh bl σ σ₀ g A I = .ok (.success (cA', σ', gas, substate) output)) :
    ∃ locals call, CallBound (initState cA gh bl σ σ₀ (.ofUInt256 g) A I) locals call ∧
      entryKeys call.entry = calldataScope I := by
  have length := runtime_success_length code success
  have known := runtime_success_selector (g := Sat256.ofUInt256 g) code bounded success
  simp only [runtimeSelectors, List.mem_cons, List.not_mem_nil, or_false] at known
  rcases known with seq | batch | root | number | withdrawal | backing | pending | deposit | claims
  · refine ⟨_, _, sequencer_getter_call_bound _ length seq, ?_⟩
    simp [entryKeys, calldataScope, seq]
  · have writable : I.perm = true := by
      cases mode : I.perm with
      | true => rfl
      | false => exact False.elim (batch_static_no_success code mode bounded batch success)
    refine ⟨_, _, batch_accepted_call_bound code writable bounded batch success, ?_⟩
    simp [entryKeys, calldataScope, batch, batchFromCalldata]
  · refine ⟨_, _, scalar_getter_call_bound _ .stateRoot length root, ?_⟩
    simp [entryKeys, scalarModelGetter, calldataScope, root]
  · refine ⟨_, _, scalar_getter_call_bound _ .batchNumber length number, ?_⟩
    simp [entryKeys, scalarModelGetter, calldataScope, number]
  · have writable : I.perm = true := by
      cases mode : I.perm with
      | true => rfl
      | false => exact False.elim (withdrawal_static_no_success code mode bounded withdrawal success)
    refine ⟨_, _, withdrawal_accepted_call_bound code writable bounded withdrawal success, ?_⟩
    simp [entryKeys, calldataScope, withdrawal, withdrawalOwnerFromCalldata]
  · refine ⟨_, _, scalar_getter_call_bound _ .backing length backing, ?_⟩
    simp [entryKeys, scalarModelGetter, calldataScope, backing]
  · obtain ⟨_, size, signedBound, canonical, _⟩ :=
      mapping_getter_xi_success (g := Sat256.ofUInt256 g) .pendingDeposits code bounded pending success
    refine ⟨_, _, mapping_getter_call_bound _ .pendingDeposits size signedBound canonical pending, ?_⟩
    simp [entryKeys, mappingModelGetter, calldataScope, pending]
    rfl
  · have writable : I.perm = true := by
      cases mode : I.perm with
      | true => rfl
      | false => exact False.elim (deposit_static_no_success code mode bounded deposit success)
    refine ⟨_, _, deposit_accepted_call_bound code writable bounded deposit success, ?_⟩
    simp [entryKeys, calldataScope, deposit]
  · obtain ⟨_, size, signedBound, canonical, _⟩ :=
      mapping_getter_xi_success (g := Sat256.ofUInt256 g) .pendingWithdrawals code bounded claims success
    refine ⟨_, _, mapping_getter_call_bound _ .pendingWithdrawals size signedBound canonical claims, ?_⟩
    simp [entryKeys, mappingModelGetter, calldataScope, claims]
    rfl

end Rollup.EVM
