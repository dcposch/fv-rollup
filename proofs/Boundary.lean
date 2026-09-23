import semantics.Boundary
import proofs.CallbackProjection
import proofs.WithdrawalBalances
import proofs.ProjectionEquivalence

open Ethereum Ethereum.EVM Solm Reasoning.Theory

namespace Rollup.EVM

/-- Projection reads accounts; execution metadata does not change the model state. -/
theorem project_boundary (state : Ethereum.State) (self : Address) (keys : AccessScope) :
    project state self keys = boundaryModel self state.accountMap keys := by
  exact project_equiv (accountMapEquiv.refl state.accountMap) self keys

theorem boundary_ready_of_state {state : Ethereum.State} {keys : AccessScope}
    (code : OwnCode state) (world : WorldBounded state)
    (ready : StorageReady state state.executionEnv.codeOwner keys)
    (unlocked : readWord state state.executionEnv.codeOwner ⟨6⟩ = ⟨0⟩) :
    BoundaryReady state.executionEnv.codeOwner state.accountMap keys := by
  exact ⟨⟨rfl, code.2⟩, world, ready, unlocked⟩

/-- At a call boundary the account contains the pinned code. -/
theorem BoundaryReady.pinned {self accounts keys} (ready : BoundaryReady self accounts keys) :
    (accounts.findD self default).code = runtimeBytecode := ownCode_default ready.1

theorem BoundaryReady.world {self accounts keys} (ready : BoundaryReady self accounts keys) :
    worldEth accounts < wordLimit := (worldBounded_iff_worldEth (accountView self accounts)).mp ready.2.1

theorem boundary_balance_bound (self : Address) (accounts : AccountMap) (keys : AccessScope) :
    (boundaryModel self accounts keys).eth < wordLimit := by
  change (project (accountView self accounts) self keys).eth < wordLimit
  rw [project_ethLedger]
  exact (accounts.findD self default).balance.val.isLt

/-- Extend a finite scope without changing any account credit. -/
theorem boundary_model_extend {self accounts small large}
    (ready : BoundaryReady self accounts small)
    (subset : small ⊆ large) (distinct : NoAlias large) :
    boundaryModel self accounts large = boundaryModel self accounts small :=
  project_extend subset distinct ready.2.2.1.2.2

/-- New keys preserve the boundary conditions when their slots are distinct. -/
theorem boundary_ready_extend {self accounts small large}
    (ready : BoundaryReady self accounts small)
    (subset : small ⊆ large) (distinct : NoAlias large) :
    BoundaryReady self accounts large := by
  exact ⟨ready.1, ready.2.1,
    ⟨Finset.Subset.trans ready.2.2.1.1 subset, distinct,
      sparse_mono subset ready.2.2.1.2.2⟩, ready.2.2.2⟩

end Rollup.EVM
