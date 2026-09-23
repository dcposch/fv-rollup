import semantics.Environment
import proofs.DepositCorrespondence
import proofs.DepositRefinement
import proofs.ProjectionEquivalence
import proofs.Calls

open Solm Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Rollup.EVM

/-- An accepted EVM deposit has the exact labeled model effect. -/
theorem deposit_evm_effect {cA gh bl σ σ₀ A I} {g : UInt256}
    {cA' σ' gas substate output} (owner : Address) (keys : AccessScope)
    (code : I.code = runtimeBytecode) (writable : I.perm = true)
    (bounded : I.calldata.size < UInt256.size)
    (selector : solcSelectorWord I = ⟨0xf340fa01⟩)
    (decoded : calldataWord I.calldata 4 = UInt256.ofNat owner.val)
    (bound : CallBound (initState cA gh bl σ σ₀ (.ofUInt256 g) A I) (depositLocals owner)
      ⟨I.source, I.weiValue.toNat, .deposit owner⟩)
    (accesses : entryKeys (.deposit owner) ⊆ keys)
    (own : OwnCode (initState cA gh bl σ σ₀ (.ofUInt256 g) A I))
    (world : WorldBounded (initState cA gh bl σ σ₀ (.ofUInt256 g) A I))
    (ready : StorageReady (initState cA gh bl σ σ₀ (.ofUInt256 g) A I) I.codeOwner keys)
    (funds : I.weiValue.toNat ≤
      (project (initState cA gh bl σ σ₀ (.ofUInt256 g) A I) I.codeOwner keys).eth)
    (success : Ξ cA gh bl σ σ₀ g A I = .ok (.success (cA', σ', gas, substate) output)) :
    let result := project (initState cA' gh bl σ' σ₀ (.ofUInt256 gas) substate I)
      I.codeOwner keys
    let initial := beforeCall (initState cA gh bl σ σ₀ (.ofUInt256 g) A I) keys
    DepositEnabled initial owner I.weiValue.toNat ∧
      result = deposit initial owner I.weiValue.toNat ∧ output = ByteArray.empty := by
  obtain ⟨frame, run, _, maps, empty⟩ := deposit_success_correspondence owner
    code writable bounded selector decoded (accountMapEquiv.refl σ) success
  have refined := deposit_source_refines _ _ (depositLocals owner) frame I.source owner
    I.weiValue.toNat none keys bound accesses own world ready funds run
  obtain ⟨_, _, _, _, _, result, payments, _, step, _⟩ := refined
  obtain ⟨enabled, state, _, _⟩ := successful_deposit_exact step
  have same := project_equiv
    (left := initState cA' gh bl σ' σ₀ (.ofUInt256 gas) substate I) maps I.codeOwner keys
  exact ⟨enabled, same.trans state, empty⟩

/-- An accepted EVM deposit preserves custody under the finite storage conditions. -/
theorem deposit_evm_custody {cA gh bl σ σ₀ A I} {g : UInt256}
    {cA' σ' gas substate output} (owner : Address) (keys : AccessScope)
    (code : I.code = runtimeBytecode) (writable : I.perm = true)
    (bounded : I.calldata.size < UInt256.size)
    (selector : solcSelectorWord I = ⟨0xf340fa01⟩)
    (decoded : calldataWord I.calldata 4 = UInt256.ofNat owner.val)
    (bound : CallBound (initState cA gh bl σ σ₀ (.ofUInt256 g) A I) (depositLocals owner)
      ⟨I.source, I.weiValue.toNat, .deposit owner⟩)
    (accesses : entryKeys (.deposit owner) ⊆ keys)
    (own : OwnCode (initState cA gh bl σ σ₀ (.ofUInt256 g) A I))
    (world : WorldBounded (initState cA gh bl σ σ₀ (.ofUInt256 g) A I))
    (ready : StorageReady (initState cA gh bl σ σ₀ (.ofUInt256 g) A I) I.codeOwner keys)
    (funds : I.weiValue.toNat ≤
      (project (initState cA gh bl σ σ₀ (.ofUInt256 g) A I) I.codeOwner keys).eth)
    (safe : Safe (beforeCall (initState cA gh bl σ σ₀ (.ofUInt256 g) A I) keys))
    (success : Ξ cA gh bl σ σ₀ g A I = .ok (.success (cA', σ', gas, substate) output)) :
    let result := project (initState cA' gh bl σ' σ₀ (.ofUInt256 gas) substate I)
      I.codeOwner keys
    liabilities result ≤ result.eth := by
  obtain ⟨enabled, state, _⟩ := deposit_evm_effect owner keys code writable bounded
    selector decoded bound accesses own world ready funds success
  have solvent := (callStep_safe safe (CallStep.deposit (caller := I.source) enabled)).1
  dsimp only
  rw [state]
  simpa [Solvent, reserved, deposit] using solvent

end Rollup.EVM
