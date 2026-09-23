import proofs.BatchABI

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Rollup.EVM

/-- Valid batch calldata binds the actual caller, value, and all seven arguments. -/
theorem batch_call_bound (evm : Ethereum.State)
    (length : 228 ≤ evm.executionEnv.calldata.size)
    (signedBound : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (depositCanonical : (calldataWord evm.executionEnv.calldata 100).toNat < _root_.EVM.addressModulus)
    (withdrawalCanonical : (calldataWord evm.executionEnv.calldata 164).toNat < _root_.EVM.addressModulus)
    (selector : solcSelectorWord evm.executionEnv = ⟨0x88af9950⟩) :
    CallBound evm (batchLocals (batchFromCalldata evm.executionEnv))
      ⟨evm.executionEnv.source, evm.executionEnv.weiValue.toNat, .executeBatch (batchFromCalldata evm.executionEnv)⟩ := by
  have dispatched := source_selector_dispatch evm.executionEnv ⟨1, by decide⟩ (by omega) selector
  refine ⟨rfl, rfl, ?_, batch_abi_decode evm.executionEnv length signedBound depositCanonical withdrawalCanonical, ?_⟩
  · exact selectorDispatchMsg_eq_some_of_dispatchMsg_eq_some (by rfl) (by rfl) dispatched
  · rfl

/-- Every accepted writable bytecode batch has the matching full source call. -/
theorem batch_accepted_equivalence {cA gh bl σ σ_solm σ₀ A I} {g : UInt256}
    {cA' σ' gas substate output}
    (code : I.code = runtimeBytecode) (writable : I.perm = true)
    (bounded : I.calldata.size < UInt256.size)
    (selector : solcSelectorWord I = ⟨0x88af9950⟩) (maps : accountMapEquiv σ σ_solm)
    (success : Ξ cA gh bl σ σ₀ g A I = .ok (.success (cA', σ', gas, substate) output)) :
    runtimeEquivalenceFor config contract cA gh bl σ σ_solm σ₀ g A I := by
  have checks := batch_xi_header (g := Sat256.ofUInt256 g) code writable bounded selector success
  have dispatched := source_selector_dispatch I ⟨1, by decide⟩ (by have := checks.length; omega) selector
  have decoded := batch_abi_decode I checks.length checks.signedBound checks.depositCanonical checks.withdrawalCanonical
  obtain ⟨source, created, accounts, outputEq⟩ := batch_accepted_source code writable bounded selector maps success
  refine reEquiv_execution dispatched decoded source ?_
  rw [success, outputEq]
  exact execResultsEquiv.success rfl rfl created accounts
    (.abi (.fallthrough rfl rfl (by
      change encodeReturnValues? [] [] = some ByteArray.empty
      simp [encodeReturnValues?, encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?]
      rfl)))

/-- A writable batch that passes its checks satisfies runtime equivalence, including out-of-gas. -/
theorem batch_checked_equivalence {cA gh bl σ σ_solm σ₀ A I} {g : UInt256}
    (code : I.code = runtimeBytecode) (writable : I.perm = true)
    (bounded : I.calldata.size < UInt256.size)
    (selector : solcSelectorWord I = ⟨0x88af9950⟩) (maps : accountMapEquiv σ σ_solm)
    (checks : BatchBytecodeChecks σ I) :
    runtimeEquivalenceFor config contract cA gh bl σ σ_solm σ₀ g A I := by
  rcases batch_xi_execution (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A) (g := g)
      code writable bounded selector checks with failed | ⟨gas, substate, success⟩
  · exact reEquiv_outOfGas failed
  · exact batch_accepted_equivalence code writable bounded selector maps success

end Rollup.EVM
