import proofs.MessageValue

open Ethereum Ethereum.EVM Solm Reasoning.Theory

namespace Rollup.EVM

/-- A funded transfer to the rollup adds surplus ETH without changing credit. -/
theorem boundary_donation (self sender : Address) (accounts : AccountMap) (value : UInt256)
    (keys : AccessScope) (ready : BoundaryReady self accounts keys)
    (different : self ≠ sender) (funds : value.toNat ≤ ethLedger accounts sender) :
    let after := sendEth self sender value true accounts
    BoundaryReady self after keys ∧
      boundaryModel self after keys = donate (boundaryModel self accounts keys) value.toNat ∧
      (boundaryModel self accounts keys).eth + value.toNat < wordLimit := by
  let after := sendEth self sender value true accounts
  have frame : CodeStorageFrame self accounts after :=
    sendEth_accountStaticStateEq self sender value true accounts self
  have world := BoundaryReady.world ready
  have balance : ethLedger after self = ethLedger accounts self + value.toNat := by
    dsimp only [after]
    rw [sendEth_ledger_ne accounts self sender value different funds world]
    simp [debit, credit, Function.update]
    intro same
    exact False.elim (different same)
  have code := CodeStorageFrame.ownCode
    (before := accountView self accounts) (after := accountView self after) frame rfl ready.1
  have storage := CodeStorageFrame.storageReady
    (before := accountView self accounts) (after := accountView self after) frame ready.2.2.1
  have unlocked : readWord (accountView self after) self ⟨6⟩ = ⟨0⟩ := by
    rw [← CodeStorageFrame.readWord (before := accountView self accounts)
      (after := accountView self after) frame]
    exact ready.2.2.2
  have bounded : WorldBounded (accountView self after) := by
    apply (worldBounded_iff_worldEth (accountView self after)).mpr
    change worldEth (sendEth self sender value true accounts) < wordLimit
    rwa [sendEth_world _ _ _ _ _ funds world]
  have projected := CodeStorageFrame.project
    (before := accountView self accounts) (after := accountView self after) frame keys
  have eth : (boundaryModel self after keys).eth =
      (boundaryModel self accounts keys).eth + value.toNat := by
    simpa only [boundaryModel, project_ethLedger, accountView] using balance
  refine ⟨⟨code, bounded, storage, unlocked⟩, ?_, ?_⟩
  · change boundaryModel self after keys =
      { boundaryModel self accounts keys with eth := (boundaryModel self after keys).eth } at projected
    rw [eth] at projected
    exact projected
  · rw [← eth]
    exact boundary_balance_bound self after keys

end Rollup.EVM
