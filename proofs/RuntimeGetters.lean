import proofs.RuntimeScalarDispatch
import proofs.RuntimeSequencerGetter
import proofs.RuntimeMappingDispatch

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Rollup.EVM

/-- Accepted getters preserve all accounts in writable and static calls. -/
theorem getter_xi_preserves_accounts {cA gh bl σ σ₀ A I} {g : Sat256}
    {cA' σ' gas substate output} (code : I.code = runtimeBytecode)
    (bounded : I.calldata.size < UInt256.size)
    (getter : solcSelectorWord I ∈ ([⟨0x5c1bba38⟩, ⟨0x9588eca2⟩, ⟨0xba873065⟩,
      ⟨0xc9503fe2⟩, ⟨0xeb3349b9⟩, ⟨0xf3f43703⟩] : List UInt256))
    (success : Ξ cA gh bl σ σ₀ g.toUInt256 A I = .ok (.success (cA', σ', gas, substate) output)) :
    I.weiValue = ⟨0⟩ ∧ cA' = cA ∧ σ' = σ := by
  have length : 4 ≤ I.calldata.size := by
    by_contra short
    have rejected := runtime_short_calldata (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (g := g) code (by omega)
    rcases rejected.xiResult code with failed | ⟨gas', data, actual⟩
    · rw [success] at failed
      cases failed
    · rw [success] at actual
      cases actual
  simp only [List.mem_cons, List.not_mem_nil, or_false] at getter
  rcases getter with seq | root | number | backing | pending | claims
  · have result := sequencer_getter_xi_success code length bounded seq success
    exact ⟨result.1, result.2.1, result.2.2.1⟩
  · have result := scalar_getter_xi_success .stateRoot code length bounded root success
    exact ⟨result.1, result.2.1, result.2.2.1⟩
  · have result := scalar_getter_xi_success .batchNumber code length bounded number success
    exact ⟨result.1, result.2.1, result.2.2.1⟩
  · have result := scalar_getter_xi_success .backing code length bounded backing success
    exact ⟨result.1, result.2.1, result.2.2.1⟩
  · have result := mapping_getter_xi_success .pendingDeposits code bounded pending success
    exact ⟨result.1, result.2.2.2.2.1, result.2.2.2.2.2.1⟩
  · have result := mapping_getter_xi_success .pendingWithdrawals code bounded claims success
    exact ⟨result.1, result.2.2.2.2.1, result.2.2.2.2.2.1⟩

end Rollup.EVM
