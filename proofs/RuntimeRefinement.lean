import proofs.RuntimeSource
import proofs.ProjectionEquivalence
import proofs.Calls

open Solm Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Rollup.EVM

/-- Accepted bytecode implements the model and preserves the world conditions. -/
theorem runtime_refines_model {cA gh bl σ σ₀ A I} {g : UInt256}
    {cA' σ' gas substate output} (locals : Store) (call : Call) (keys : AccessScope)
    (code : I.code = runtimeBytecode)
    (bounded : I.calldata.size < UInt256.size)
    (bound : CallBound (initState cA gh bl σ σ₀ (.ofUInt256 g) A I) locals call)
    (accesses : entryKeys call.entry ⊆ keys)
    (own : OwnCode (initState cA gh bl σ σ₀ (.ofUInt256 g) A I))
    (world : WorldBounded (initState cA gh bl σ σ₀ (.ofUInt256 g) A I))
    (ready : StorageReady (initState cA gh bl σ σ₀ (.ofUInt256 g) A I) I.codeOwner keys)
    (unlocked : readWord (initState cA gh bl σ σ₀ (.ofUInt256 g) A I) I.codeOwner ⟨6⟩ = ⟨0⟩)
    (funds : I.weiValue.toNat ≤ (project (initState cA gh bl σ σ₀ (.ofUInt256 g) A I) I.codeOwner keys).eth)
    (safe : Safe (beforeCall (initState cA gh bl σ σ₀ (.ofUInt256 g) A I) keys))
    (success : Ξ cA gh bl σ σ₀ g A I = .ok (.success (cA', σ', gas, substate) output)) :
    let finalState := initState cA' gh bl σ' σ₀ (.ofUInt256 gas) substate I
    StorageReady finalState I.codeOwner keys ∧ readWord finalState I.codeOwner ⟨6⟩ = ⟨0⟩ ∧
      OwnCode finalState ∧ WorldBounded finalState ∧
      ∃ result payments,
        CallStep (beforeCall (initState cA gh bl σ σ₀ (.ofUInt256 g) A I) keys)
          call (.success result) payments (project finalState I.codeOwner keys) ∧
        returnDataEquiv output (returnValues result) (.abi (entryTransition call.entry).returnType) := by
  obtain ⟨frame, sourceOut, values, source, maps, returned⟩ :=
    runtime_accepted_source locals call code bounded bound success
  obtain ⟨sourceReady, sourceUnlocked, environment, sourceCode, sourceWorld,
      result, payments, valuesEq, step, _⟩ :=
    source_refines_model _ sourceOut locals frame call values keys bound accesses own world ready
      unlocked funds safe source
  let finalState := initState cA' gh bl σ' σ₀ (.ofUInt256 gas) substate I
  have same : accountMapEquiv finalState.accountMap sourceOut.accountMap := maps
  have environments : finalState.executionEnv = sourceOut.executionEnv := environment.symm
  refine ⟨(storageReady_equiv same I.codeOwner keys).mpr sourceReady, ?_,
    (ownCode_equiv same environments).mpr sourceCode, (worldBounded_equiv same).mpr sourceWorld,
    result, payments, ?_, ?_⟩
  · rw [readWord_equiv same]
    exact sourceUnlocked
  · rw [project_equiv same]
    exact step
  · rwa [← valuesEq]

/-- Accepted EVM calls preserve all model safety predicates. -/
theorem runtime_preserves_safe {cA gh bl σ σ₀ A I} {g : UInt256}
    {cA' σ' gas substate output} (locals : Store) (call : Call) (keys : AccessScope)
    (code : I.code = runtimeBytecode)
    (bounded : I.calldata.size < UInt256.size)
    (bound : CallBound (initState cA gh bl σ σ₀ (.ofUInt256 g) A I) locals call)
    (accesses : entryKeys call.entry ⊆ keys)
    (own : OwnCode (initState cA gh bl σ σ₀ (.ofUInt256 g) A I))
    (world : WorldBounded (initState cA gh bl σ σ₀ (.ofUInt256 g) A I))
    (ready : StorageReady (initState cA gh bl σ σ₀ (.ofUInt256 g) A I) I.codeOwner keys)
    (unlocked : readWord (initState cA gh bl σ σ₀ (.ofUInt256 g) A I) I.codeOwner ⟨6⟩ = ⟨0⟩)
    (funds : I.weiValue.toNat ≤ (project (initState cA gh bl σ σ₀ (.ofUInt256 g) A I) I.codeOwner keys).eth)
    (safe : Safe (beforeCall (initState cA gh bl σ σ₀ (.ofUInt256 g) A I) keys))
    (success : Ξ cA gh bl σ σ₀ g A I = .ok (.success (cA', σ', gas, substate) output)) :
    Safe (project (initState cA' gh bl σ' σ₀ (.ofUInt256 gas) substate I) I.codeOwner keys) := by
  obtain ⟨_, _, _, _, _, _, step, _⟩ := runtime_refines_model locals call keys code
    bounded bound accesses own world ready unlocked funds safe success
  exact callStep_safe safe step

end Rollup.EVM
