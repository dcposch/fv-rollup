import proofs.WithdrawalEquivalence
import proofs.DepositDispatch
import proofs.BatchEquivalence
import proofs.GetterEquivalence
import proofs.DispatchRejection
import proofs.CreationRefinement

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Rollup.EVM

/-- Every writable runtime entry has the same source outcome, under EquiVM's equivalence relation. -/
theorem runtime_equivalence_for {cA gh bl σ σ_solm σ₀ A I} {g : UInt256}
    (code : I.code = runtimeBytecode) (writable : I.perm = true)
    (bounded : I.calldata.size < UInt256.size) (maps : accountMapEquiv σ σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ σ_solm σ₀ g A I := by
  by_cases four : 4 ≤ I.calldata.size
  · by_cases known : solcSelectorWord I ∈ runtimeSelectors
    · simp only [runtimeSelectors, List.mem_cons, List.not_mem_nil, or_false] at known
      rcases known with sequencer | batch | root | number | withdrawal | backing | pending | deposit | claims
      · exact sequencer_getter_correct code four bounded sequencer maps
      · exact batch_correct code writable four bounded batch maps
      · exact scalar_getter_correct .stateRoot code four bounded root maps
      · exact scalar_getter_correct .batchNumber code four bounded number maps
      · exact withdrawal_correct code writable four bounded withdrawal maps
      · exact scalar_getter_correct .backing code four bounded backing maps
      · exact mapping_getter_correct .pendingDeposits code four bounded pending maps
      · exact deposit_correct code writable four bounded deposit maps
      · exact mapping_getter_correct .pendingWithdrawals code four bounded claims maps
    · exact unknown_selector_correct code bounded known
  · exact short_calldata_correct code (by omega)

/-- The pinned runtime matches the source for all writable calls. -/
theorem runtime_correct : runtimeEquivalence config runtimeBytecode contract := by
  refine .intro ?_
  intro cA gh bl σ σ_solm σ₀ g A I code bounded writable maps
  exact runtime_equivalence_for code writable bounded maps

/-- Discharge creation and runtime bytecode equivalence. Model refinement remains separate. -/
theorem bytecode_correct : BytecodeCorrect :=
  .intro constructor_correct runtime_correct

end Rollup.EVM
