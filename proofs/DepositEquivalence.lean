import proofs.DepositAgreement
import Reasoning.Dispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Rollup.EVM

/-- A decoded deposit has equivalent EVM and source outcomes. -/
theorem deposit_decoded_equivalence {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (code : I.code = runtimeBytecode) (writable : I.perm = true)
    (bounded : I.calldata.size < UInt256.size)
    (selector : solcSelectorWord I = ⟨0xf340fa01⟩)
    (dispatch : dispatchMsg contract I.calldata = some contract.transitions[0]!)
    (length : 36 ≤ I.calldata.size) (signedBound : I.calldata.size < 2 ^ 255 + 4)
    (canonical : (calldataWord I.calldata 4).toNat < _root_.EVM.addressModulus)
    (maps : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let owner := AccountAddress.ofNat (calldataWord I.calldata 4).toNat
  let initial := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have decodedWord : calldataWord I.calldata 4 = UInt256.ofNat owner.val := by
    have same := keyValueToWord_address_of_canonical _ canonical
    rw [keyValueToWord_address] at same
    exact same.symm
  have decodedABI : decodeCalldataWithMode config.abiDecodeMode
      (contract.transitions[0]!.params.map Param.name)
      (transitionSignature contract.transitions[0]!).paramTypes I.calldata =
        some (depositLocals owner) :=
    decodeCalldata_address_ok length signedBound canonical
  by_cases checks : DepositExecutionChecks initial owner
  · obtain ⟨unlocked, nonzero, different, value, fits⟩ :=
      (deposit_checks_init (g := Sat256.ofUInt256 g) owner maps).mp checks
    rw [← decodedWord] at nonzero different fits
    have returned := deposit_bytecode_execution (cA := cA) (gh := gh) (bl := bl)
      (σ := σ_evm) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g)
      code writable length signedBound bounded selector canonical nonzero different value unlocked fits
    rcases returned with outOfGas | ⟨state, result, accounts⟩
    · exact reEquiv_outOfGas (Xi_error_of_X (g := g) (by
        rw [← code] at outOfGas
        simpa [Sat256.ofUInt256] using outOfGas))
    · have success := Xi_success_of_X (g := g) (by
        rw [← code] at result
        simpa [Sat256.ofUInt256] using result)
      obtain ⟨frame, source, created, equivalent, _⟩ :=
        deposit_success_correspondence owner code writable bounded selector decodedWord maps success
      refine reEquiv_execution dispatch decodedABI source ?_
      rw [success]
      exact execResultsEquiv.success rfl rfl created equivalent
        (.abi (.fallthrough rfl rfl (by
          change encodeReturnValues? [] [] = some ByteArray.empty
          simp [encodeReturnValues?, encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?]
          rfl)))
  · have rejected : RDrev runtimeBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) := by
      rcases deposit_bytecode_classification (cA := cA) (gh := gh) (bl := bl)
          (σ := σ_evm) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g)
          code writable bounded selector with rejected | accepted
      · exact rejected
      · obtain ⟨_, _, _, nonzero, different, value, unlocked, fits, _⟩ := accepted
        rw [decodedWord] at nonzero different fits
        exact False.elim (checks ((deposit_checks_init owner maps).mpr
          ⟨unlocked, nonzero, different, value, fits⟩))
    have source := (exact_function_revert (deposit_body_rejection initial owner checks)).1
    have equivalent := rejected.reEquivExecutionRevert code dispatch decodedABI source
    simpa [Sat256.ofUInt256, Sat256.toUInt256] using equivalent

end Rollup.EVM
