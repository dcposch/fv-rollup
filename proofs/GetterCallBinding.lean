import proofs.GetterEquivalence
import proofs.RuntimeUnknownSelector

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Rollup.EVM

/-- Accepted runtime execution has at least four selector bytes. -/
theorem runtime_success_length {cA gh bl σ σ₀ A I} {g : UInt256}
    {cA' σ' gas substate output} (code : I.code = runtimeBytecode)
    (success : Ξ cA gh bl σ σ₀ g A I = .ok (.success (cA', σ', gas, substate) output)) :
    4 ≤ I.calldata.size := by
  by_contra short
  have rejected := runtime_short_calldata (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) code (by omega)
  rcases rejected.xiResult code with failed | ⟨gas', data, actual⟩
  · change Ξ cA gh bl σ σ₀ g A I = _ at failed
    rw [success] at failed
    cases failed
  · change Ξ cA gh bl σ σ₀ g A I = _ at actual
    rw [success] at actual
    cases actual

/-- Scalar getter calldata binds the actual caller and value. -/
theorem scalar_getter_call_bound (evm : Ethereum.State) (getter : ScalarGetter)
    (length : 4 ≤ evm.executionEnv.calldata.size)
    (selector : solcSelectorWord evm.executionEnv = scalarSelector getter) :
    CallBound evm (getterLocals (scalarModelGetter getter))
      ⟨evm.executionEnv.source, evm.executionEnv.weiValue.toNat, .read (scalarModelGetter getter)⟩ := by
  have dispatched : dispatchMsg contract evm.executionEnv.calldata =
      some (entryTransition (.read (scalarModelGetter getter))) := by
    cases getter with
    | stateRoot => exact source_selector_dispatch evm.executionEnv ⟨4, by decide⟩ length selector
    | batchNumber => exact source_selector_dispatch evm.executionEnv ⟨5, by decide⟩ length selector
    | backing => exact source_selector_dispatch evm.executionEnv ⟨6, by decide⟩ length selector
  refine ⟨rfl, rfl, ?_, ?_, ?_⟩
  · exact selectorDispatchMsg_eq_some_of_dispatchMsg_eq_some (by rfl) (by rfl) dispatched
  · cases getter <;> exact decodeCalldata_empty_ok length
  · cases getter <;> rfl

/-- Sequencer getter calldata binds the actual caller and value. -/
theorem sequencer_getter_call_bound (evm : Ethereum.State)
    (length : 4 ≤ evm.executionEnv.calldata.size)
    (selector : solcSelectorWord evm.executionEnv = ⟨0x5c1bba38⟩) :
    CallBound evm (getterLocals .sequencer)
      ⟨evm.executionEnv.source, evm.executionEnv.weiValue.toNat, .read .sequencer⟩ := by
  have dispatched := source_selector_dispatch evm.executionEnv ⟨3, by decide⟩ length selector
  refine ⟨rfl, rfl, ?_, decodeCalldata_empty_ok length, rfl⟩
  exact selectorDispatchMsg_eq_some_of_dispatchMsg_eq_some (by rfl) (by rfl) dispatched

/-- Credit getter calldata also binds its owner argument. -/
theorem mapping_getter_call_bound (evm : Ethereum.State) (getter : MappingGetter)
    (length : 36 ≤ evm.executionEnv.calldata.size)
    (signedBound : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (canonical : (calldataWord evm.executionEnv.calldata 4).toNat < _root_.EVM.addressModulus)
    (selector : solcSelectorWord evm.executionEnv = mappingSelector getter) :
    let owner := AccountAddress.ofNat (calldataWord evm.executionEnv.calldata 4).toNat
    CallBound evm (getterLocals (mappingModelGetter getter owner))
      ⟨evm.executionEnv.source, evm.executionEnv.weiValue.toNat, .read (mappingModelGetter getter owner)⟩ := by
  let owner := AccountAddress.ofNat (calldataWord evm.executionEnv.calldata 4).toNat
  have dispatched : dispatchMsg contract evm.executionEnv.calldata =
      some (entryTransition (.read (mappingModelGetter getter owner))) := by
    cases getter with
    | pendingDeposits => exact source_selector_dispatch evm.executionEnv ⟨7, by decide⟩ (by omega) selector
    | pendingWithdrawals => exact source_selector_dispatch evm.executionEnv ⟨8, by decide⟩ (by omega) selector
  refine ⟨rfl, rfl, ?_, ?_, ?_⟩
  · exact selectorDispatchMsg_eq_some_of_dispatchMsg_eq_some (by rfl) (by rfl) dispatched
  · cases getter <;> exact decodeCalldata_address_ok length signedBound canonical
  · cases getter <;> rfl

end Rollup.EVM
