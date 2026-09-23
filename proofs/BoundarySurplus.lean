import proofs.Boundary
import proofs.WorldExecution
import proofs.Calls

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- Fixed code and storage with surplus ETH give a model donation step. -/
theorem boundary_surplus_frame {self : Address} {before after : AccountMap} {keys : AccessScope}
    (ready : BoundaryReady self before keys)
    (frame : CodeStorageFrame self before after) (balances : EthFrame self before after) :
    BoundaryReady self after keys ∧
      TraceStep (boundaryModel self before keys) (boundaryModel self after keys) := by
  have code := CodeStorageFrame.ownCode
    (before := accountView self before) (after := accountView self after) frame rfl ready.1
  have storage := CodeStorageFrame.storageReady
    (before := accountView self before) (after := accountView self after) frame ready.2.2.1
  have unlocked : readWord (accountView self after) self ⟨6⟩ = ⟨0⟩ := by
    rw [← CodeStorageFrame.readWord (before := accountView self before)
      (after := accountView self after) frame]
    exact ready.2.2.2
  have bounded : WorldBounded (accountView self after) :=
    (worldBounded_iff_worldEth (accountView self after)).mpr
      (balances.1.trans_lt (BoundaryReady.world ready))
  have eth : (boundaryModel self before keys).eth ≤ (boundaryModel self after keys).eth := by
    simpa only [boundaryModel, project_ethLedger, accountView] using balances.2
  have projected := CodeStorageFrame.project
    (before := accountView self before) (after := accountView self after) frame keys
  change boundaryModel self after keys =
    { boundaryModel self before keys with eth := (boundaryModel self after keys).eth } at projected
  have model : boundaryModel self after keys = donate (boundaryModel self before keys)
      ((boundaryModel self after keys).eth - (boundaryModel self before keys).eth) := by
    simpa only [donate, Nat.add_sub_of_le eth] using projected
  refine ⟨⟨code, bounded, storage, unlocked⟩, ?_⟩
  rw [model]
  apply TraceStep.donation
  rw [Nat.add_sub_of_le eth]
  exact boundary_balance_bound self after keys

end Rollup.EVM
