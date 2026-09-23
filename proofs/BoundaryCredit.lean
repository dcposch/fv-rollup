import proofs.BoundaryTransfer

open Ethereum Ethereum.EVM Reasoning.Theory

set_option maxRecDepth 2048

namespace Rollup.EVM

/-- A credit changes only the recipient's ETH balance. -/
theorem increase_balance_ledger (accounts : AccountMap) (owner : Address) (value : UInt256)
    (bounded : ethLedger accounts owner + value.toNat < UInt256.size) :
    ethLedger (accounts.increaseBalance owner value) =
      credit (ethLedger accounts) owner value.toNat := by
  cases found : accounts.find? owner with
  | none =>
    have old : ethLedger accounts owner = 0 := by
      rw [ethLedger_lookup, found]
      rfl
    simp only [AccountMap.increaseBalance, found, ethLedger_insert, credit, old, Nat.zero_add]
  | some account =>
    have old : ethLedger accounts owner = account.balance.toNat := by
      simp [ethLedger, Batteries.RBMap.findD, found]
    simp only [AccountMap.increaseBalance, found, ethLedger_insert, credit, old]
    congr 1
    rw [uadd_toNat, Nat.mod_eq_of_lt (by simpa only [old] using bounded)]

/-- A bounded credit increases total ETH by its amount. -/
theorem increase_balance_world (accounts : AccountMap) (owner : Address) (value : UInt256)
    (bounded : ethLedger accounts owner + value.toNat < UInt256.size) :
    worldEth (accounts.increaseBalance owner value) = worldEth accounts + value.toNat := by
  unfold worldEth
  rw [increase_balance_ledger accounts owner value bounded, total_credit]

/-- A balance credit preserves code and both storage maps. -/
theorem increase_balance_storage (accounts : AccountMap) (owner self : Address) (value : UInt256) :
    CodeStorageFrame self accounts (accounts.increaseBalance owner value) := by
  apply accountStaticStateEq_of_storage_code
  · cases found : accounts.find? owner <;>
      simp only [AccountMap.increaseBalance, found] <;>
      apply accountStorageStateEq_insert_preserve <;>
      simp [Batteries.RBMap.findD, found]
  · cases found : accounts.find? owner <;>
      simp only [AccountMap.increaseBalance, found] <;>
      apply accountCodeStateEq_insert_preserve <;>
      simp [Batteries.RBMap.findD, found]

/-- A code and storage frame permits surplus ETH if the final world remains bounded. -/
theorem boundary_bounded_surplus_refines {self : Address} {before after : AccountMap}
    {keys : AccessScope} (ready : BoundaryReady self before keys)
    (safe : Safe (boundaryModel self before keys)) (frame : CodeStorageFrame self before after)
    (bounded : worldEth after < wordLimit) (balance : ethLedger before self ≤ ethLedger after self) :
    BoundaryRefines self keys before after := by
  have code := CodeStorageFrame.ownCode
    (before := accountView self before) (after := accountView self after) frame rfl ready.1
  have storage := CodeStorageFrame.storageReady
    (before := accountView self before) (after := accountView self after) frame ready.2.2.1
  have unlocked : readWord (accountView self after) self ⟨6⟩ = ⟨0⟩ := by
    rw [← CodeStorageFrame.readWord (before := accountView self before)
      (after := accountView self after) frame]
    exact ready.2.2.2
  have world : WorldBounded (accountView self after) :=
    (worldBounded_iff_worldEth (accountView self after)).mpr bounded
  have eth : (boundaryModel self before keys).eth ≤ (boundaryModel self after keys).eth := by
    simpa only [boundaryModel, project_ethLedger, accountView] using balance
  have projected := CodeStorageFrame.project
    (before := accountView self before) (after := accountView self after) frame keys
  change boundaryModel self after keys =
    { boundaryModel self before keys with eth := (boundaryModel self after keys).eth } at projected
  have model : boundaryModel self after keys = donate (boundaryModel self before keys)
      ((boundaryModel self after keys).eth - (boundaryModel self before keys).eth) := by
    simpa only [donate, Nat.add_sub_of_le eth] using projected
  have effect : TraceStep (boundaryModel self before keys) (boundaryModel self after keys) := by
    rw [model]
    apply TraceStep.donation
    rw [Nat.add_sub_of_le eth]
    exact boundary_balance_bound self after keys
  have trace := CallTrace.next CallTrace.initial effect
  exact ⟨⟨code, world, storage, unlocked⟩, callTrace_safe safe trace, trace⟩

/-- A bounded transaction refund or fee credit preserves the rollup boundary. -/
theorem boundary_credit_refines (self owner : Address) (accounts : AccountMap) (value : UInt256)
    (keys : AccessScope) (ready : BoundaryReady self accounts keys)
    (safe : Safe (boundaryModel self accounts keys))
    (bounded : worldEth accounts + value.toNat < wordLimit) :
    BoundaryRefines self keys accounts (accounts.increaseBalance owner value) := by
  have ownerBound : ethLedger accounts owner + value.toNat < UInt256.size := by
    have part : ethLedger accounts owner ≤ worldEth accounts :=
      balance_le_total (ethLedger accounts) owner
    change worldEth accounts + value.toNat < UInt256.size at bounded
    omega
  apply boundary_bounded_surplus_refines ready safe (increase_balance_storage accounts owner self value)
  · rw [increase_balance_world accounts owner value ownerBound]
    exact bounded
  · rw [increase_balance_ledger accounts owner value ownerBound]
    by_cases same : self = owner
    · subst self
      simp only [credit, Function.update_self]
      exact Nat.le_add_right _ _
    · simp only [credit, Function.update_of_ne same, le_refl]

end Rollup.EVM
