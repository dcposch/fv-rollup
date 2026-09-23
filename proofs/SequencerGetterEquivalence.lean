import proofs.RuntimeSequencerGetter
import proofs.GetterValues
import Reasoning.Dispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Rollup.EVM

/-- The sequencer getter has equivalent EVM and source outcomes. -/
theorem sequencer_getter_equivalence_for {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (code : I.code = runtimeBytecode)
    (length : 4 ≤ I.calldata.size) (bounded : I.calldata.size < UInt256.size)
    (selector : solcSelectorWord I = ⟨0x5c1bba38⟩)
    (dispatch : dispatchMsg contract I.calldata = some (entryTransition (.read .sequencer)))
    (maps : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have decoded : decodeCalldataWithMode config.abiDecodeMode
      ((entryTransition (.read .sequencer)).params.map Param.name)
      (transitionSignature (entryTransition (.read .sequencer))).paramTypes
      I.calldata = some (getterLocals .sequencer) := decodeCalldata_empty_ok length
  obtain ⟨_, _, reached⟩ := sequencer_getter_dispatch (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) code length bounded selector
  by_cases value : I.weiValue = ⟨0⟩
  · have returned := sequencer_getter_return [⟨0x5c1bba38⟩] (by decide) value reached
    have source := (getter_source_exact (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
      .sequencer value).1
    have word : solcSlotWord σ_solm I ⟨0⟩ = solcSlotWord σ_evm I ⟨0⟩ :=
      (accountMapEquiv_storage_findD maps I.codeOwner ⟨0⟩ ⟨0⟩).symm
    have values : some [getterValue (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        .sequencer] = some [.address (AccountAddress.ofNat
          (UInt256.land (solcSlotWord σ_evm I ⟨0⟩) solcAddrMask).toNat)] := by
      change some [Value.address (AccountAddress.ofNat
        (UInt256.land (solcSlotWord σ_solm I ⟨0⟩) solcAddrMask).toNat)] = _
      rw [word]
    exact returned.reEquivExecutionTransport code dispatch decoded source values maps
      (returnEquiv_of_encode (solcAddressReturnEncoding rfl _))
  · have rejected := sequencer_getter_nonpayable [⟨0x5c1bba38⟩] (by decide) value reached
    have source : ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (getterLocals .sequencer) (entryTransition (.read .sequencer)).body .reverted :=
      .execBlockRevert (.consRevert (.requireFalse (evalCallvalueEq_false value)))
    exact rejected.reEquivExecutionRevert code dispatch decoded source

end Rollup.EVM
