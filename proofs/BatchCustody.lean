import proofs.BatchAcceptedEquivalence
import proofs.BatchRefinement
import proofs.ProjectionEquivalence
import proofs.Calls

open Solm Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Rollup.EVM

/-- An accepted EVM batch has the exact authorized model effect. -/
theorem batch_evm_effect {cA gh bl σ σ₀ A I} {g : UInt256}
    {cA' σ' gas substate output} (keys : AccessScope)
    (code : I.code = runtimeBytecode) (writable : I.perm = true)
    (bounded : I.calldata.size < UInt256.size)
    (selector : solcSelectorWord I = ⟨0x88af9950⟩)
    (accesses : entryKeys (.executeBatch (batchFromCalldata I)) ⊆ keys)
    (own : OwnCode (initState cA gh bl σ σ₀ (.ofUInt256 g) A I))
    (world : WorldBounded (initState cA gh bl σ σ₀ (.ofUInt256 g) A I))
    (ready : StorageReady (initState cA gh bl σ σ₀ (.ofUInt256 g) A I) I.codeOwner keys)
    (success : Ξ cA gh bl σ σ₀ g A I = .ok (.success (cA', σ', gas, substate) output)) :
    let result := project (initState cA' gh bl σ' σ₀ (.ofUInt256 gas) substate I)
      I.codeOwner keys
    let initial := beforeCall (initState cA gh bl σ σ₀ (.ofUInt256 g) A I) keys
    I.weiValue = ⟨0⟩ ∧ BatchEnabled initial I.source (batchFromCalldata I) ∧
      result = executeBatch initial (batchFromCalldata I) ∧ output = ByteArray.empty := by
  have checks := batch_xi_header (g := Sat256.ofUInt256 g) code writable bounded selector success
  have bound := batch_call_bound (initState cA gh bl σ σ₀ (.ofUInt256 g) A I)
    checks.length checks.signedBound checks.depositCanonical checks.withdrawalCanonical selector
  obtain ⟨run, _, maps, empty⟩ := batch_accepted_source
    code writable bounded selector (accountMapEquiv.refl σ) success
  have refined := batch_source_refines _ _ _ _ I.source I.weiValue.toNat
    (batchFromCalldata I) none keys bound accesses own world ready run
  obtain ⟨_, _, _, _, _, result, payments, _, step, _⟩ := refined
  obtain ⟨_, enabled, state, _, _⟩ := successful_batch_exact step
  have same := project_equiv
    (left := initState cA' gh bl σ' σ₀ (.ofUInt256 gas) substate I) maps I.codeOwner keys
  exact ⟨checks.nonpayable, enabled, same.trans state, empty⟩

/-- An accepted EVM batch preserves custody under the finite storage conditions. -/
theorem batch_evm_custody {cA gh bl σ σ₀ A I} {g : UInt256}
    {cA' σ' gas substate output} (keys : AccessScope)
    (code : I.code = runtimeBytecode) (writable : I.perm = true)
    (bounded : I.calldata.size < UInt256.size)
    (selector : solcSelectorWord I = ⟨0x88af9950⟩)
    (accesses : entryKeys (.executeBatch (batchFromCalldata I)) ⊆ keys)
    (own : OwnCode (initState cA gh bl σ σ₀ (.ofUInt256 g) A I))
    (world : WorldBounded (initState cA gh bl σ σ₀ (.ofUInt256 g) A I))
    (ready : StorageReady (initState cA gh bl σ σ₀ (.ofUInt256 g) A I) I.codeOwner keys)
    (safe : Safe (beforeCall (initState cA gh bl σ σ₀ (.ofUInt256 g) A I) keys))
    (success : Ξ cA gh bl σ σ₀ g A I = .ok (.success (cA', σ', gas, substate) output)) :
    let result := project (initState cA' gh bl σ' σ₀ (.ofUInt256 gas) substate I)
      I.codeOwner keys
    liabilities result ≤ result.eth := by
  obtain ⟨_, enabled, state, _⟩ := batch_evm_effect keys code writable bounded
    selector accesses own world ready success
  have solvent := (callStep_safe safe (CallStep.batch enabled)).1
  dsimp only
  rw [state]
  simpa [Solvent, reserved, executeBatch] using solvent

end Rollup.EVM
