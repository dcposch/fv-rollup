import proofs.BatchCheckCorrespondence

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Rollup.EVM

/-- A successful bytecode batch has a source execution with equivalent accounts. -/
theorem batch_success_correspondence {cA gh bl σ σ_solm σ₀ A I} {g : UInt256}
    {cA' σ' gas substate output} (batch : Batch)
    (code : I.code = runtimeBytecode) (writable : I.perm = true)
    (bounded : I.calldata.size < UInt256.size)
    (selector : solcSelectorWord I = ⟨0x88af9950⟩)
    (binding : BatchWordBinding I batch) (maps : accountMapEquiv σ σ_solm)
    (success : Ξ cA gh bl σ σ₀ g A I = .ok (.success (cA', σ', gas, substate) output)) :
    let initial := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    let finalState := batchExecutionState initial batch
    ExecTransitionBody config contract initial (batchLocals batch) contract.transitions[1]!.body
      (.returned ⟨contract, batchClaimLocals initial batch⟩ finalState none) ∧
      cA' = finalState.createdAccounts ∧ accountMapEquiv σ' finalState.accountMap ∧
      output = ByteArray.empty := by
  obtain ⟨checks, created, accounts, outputEq⟩ := batch_xi_success (g := Sat256.ofUInt256 g) code writable bounded selector success
  let initial := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have sourceChecks := batch_checks_to_source initial batch binding ((batch_checks_equiv I maps).mp checks)
  refine ⟨batch_body_success initial batch sourceChecks, ?_, ?_, outputEq⟩
  · simpa only [batchExecutionState, batchNumberedState, batchRootedState, batchCreditedState,
      batchBackedState, batchDebitedState, batchLockedState, storageStore_createdAccounts,
      initial, initState] using created
  · change accountMapEquiv σ' (batchExecutionState initial batch).accountMap
    rw [accounts, batch_accounts_correspondence initial batch binding sourceChecks]
    exact batch_output_accounts_equiv I maps

/-- Every accepted bytecode batch has a matching source batch read from its calldata. -/
theorem batch_accepted_source {cA gh bl σ σ_solm σ₀ A I} {g : UInt256}
    {cA' σ' gas substate output}
    (code : I.code = runtimeBytecode) (writable : I.perm = true)
    (bounded : I.calldata.size < UInt256.size)
    (selector : solcSelectorWord I = ⟨0x88af9950⟩) (maps : accountMapEquiv σ σ_solm)
    (success : Ξ cA gh bl σ σ₀ g A I = .ok (.success (cA', σ', gas, substate) output)) :
    let batch := batchFromCalldata I
    let initial := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    let finalState := batchExecutionState initial batch
    ExecTransitionBody config contract initial (batchLocals batch) contract.transitions[1]!.body
      (.returned ⟨contract, batchClaimLocals initial batch⟩ finalState none) ∧
      cA' = finalState.createdAccounts ∧ accountMapEquiv σ' finalState.accountMap ∧
      output = ByteArray.empty := by
  have checks := batch_xi_header (g := Sat256.ofUInt256 g) code writable bounded selector success
  exact batch_success_correspondence (batchFromCalldata I) code writable bounded selector
    (batch_word_binding I checks.depositCanonical checks.withdrawalCanonical) maps success

end Rollup.EVM
