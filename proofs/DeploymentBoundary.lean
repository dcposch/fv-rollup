import proofs.DeploymentProjection
import proofs.Transitions

open Ethereum Ethereum.EVM Reasoning.Theory

namespace Rollup.EVM

/-- Successful deployment establishes the initial model and call-boundary conditions. -/
theorem deployment_refines_initial (d : Deployment) (sequencer : Address) (root : Root)
    (nonzero : sequencer ≠ 0)
    (fresh : d.fresh (creationBytecode ++ creationArgs (UInt256.ofNat sequencer.val) ⟨root⟩))
    (present : (d.accounts.find? d.sender).isSome)
    (world : worldEth d.accounts < wordLimit)
    {address created accounts gas substate data}
    (deployed : d.run (creationBytecode ++ creationArgs (UInt256.ofNat sequencer.val) ⟨root⟩) =
      (address, created, accounts, gas, substate, true, data)) :
    BoundaryReady address accounts fixedKeys ∧
      boundaryModel address accounts fixedKeys =
        initial address sequencer root (ethLedger d.accounts address) ∧
      Safe (boundaryModel address accounts fixedKeys) := by
  obtain ⟨addressEq, accountsEq, _⟩ := deployment_success_accounts d sequencer root nonzero fresh deployed
  have installed : accounts = installRuntime (d.writtenAccounts sequencer root) address := accountsEq
  rw [installed, addressEq]
  let code := creationBytecode ++ creationArgs (UInt256.ofNat sequencer.val) ⟨root⟩
  let self := d.address code
  have stored := deployment_written_ready d sequencer root fresh present
  have bounded : worldEth (d.writtenAccounts sequencer root) < wordLimit := by
    simpa only [worldEth, deployment_written_ethLedger d sequencer root fresh] using world
  have ready := installRuntime_ready (d.writtenAccounts sequencer root) self fixedKeys
    bounded stored.1 stored.2
  have model : boundaryModel self (installRuntime (d.writtenAccounts sequencer root) self) fixedKeys =
      initial self sequencer root (ethLedger d.accounts self) := by
    rw [installRuntime_project]
    exact deployment_written_projection d sequencer root fresh present
  refine ⟨ready, model, ?_⟩
  rw [model]
  exact initial_safe self sequencer root _ (d.accounts.findD self default).balance.val.isLt

/-- The deployed initial state supports any finite scope with distinct storage slots. -/
theorem deployment_refines_scope (d : Deployment) (sequencer : Address) (root : Root)
    (keys : AccessScope) (fixed : fixedKeys ⊆ keys) (distinct : NoAlias keys)
    (nonzero : sequencer ≠ 0)
    (fresh : d.fresh (creationBytecode ++ creationArgs (UInt256.ofNat sequencer.val) ⟨root⟩))
    (present : (d.accounts.find? d.sender).isSome)
    (world : worldEth d.accounts < wordLimit)
    {address created accounts gas substate data}
    (deployed : d.run (creationBytecode ++ creationArgs (UInt256.ofNat sequencer.val) ⟨root⟩) =
      (address, created, accounts, gas, substate, true, data)) :
    BoundaryReady address accounts keys ∧
      boundaryModel address accounts keys =
        initial address sequencer root (ethLedger d.accounts address) ∧
      Safe (boundaryModel address accounts keys) := by
  obtain ⟨ready, model, safe⟩ := deployment_refines_initial d sequencer root nonzero fresh present world deployed
  have same := boundary_model_extend ready fixed distinct
  exact ⟨boundary_ready_extend ready fixed distinct, same.trans model, same.symm ▸ safe⟩

end Rollup.EVM
