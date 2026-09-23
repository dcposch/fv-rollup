import proofs.AccountErase
import proofs.BoundaryTransfer

open Ethereum Ethereum.EVM
open scoped BigOperators

namespace Rollup.EVM

/-- Deleting an account preserves lookup at every other address. -/
theorem account_erase_other (accounts : AccountMap) (owner self : Address) (different : self ≠ owner) :
    (accounts.erase owner).find? self = accounts.find? self :=
  account_find?_erase_ne accounts owner self (accountAddress_compare_ne_eq_of_ne different)

/-- Account deletion cannot increase any ETH balance. -/
theorem ethLedger_erase_le (accounts : AccountMap) (owner query : Address) :
    ethLedger (accounts.erase owner) query ≤ ethLedger accounts query := by
  simp only [ethLedger_lookup, account_find?_erase]
  split
  · simp
  · exact Nat.le_refl _

/-- Account deletion cannot increase total ETH. -/
theorem worldEth_erase_le (accounts : AccountMap) (owner : Address) :
    worldEth (accounts.erase owner) ≤ worldEth accounts := by
  unfold worldEth total
  exact Finset.sum_le_sum (fun query _ => ethLedger_erase_le accounts owner query)

/-- Deletion of another account preserves the rollup boundary. -/
theorem boundary_erase_refines (self owner : Address) (accounts : AccountMap) (keys : AccessScope)
    (different : self ≠ owner) (ready : BoundaryReady self accounts keys)
    (safe : Safe (boundaryModel self accounts keys)) :
    BoundaryRefines self keys accounts (accounts.erase owner) := by
  have lookup := account_erase_other accounts owner self different
  apply boundary_frame_refines ready safe
  · simp only [CodeStorageFrame, Batteries.RBMap.findD, lookup, and_self]
  · refine ⟨worldEth_erase_le accounts owner, ?_⟩
    simp only [ethLedger, Batteries.RBMap.findD, lookup, le_refl]

/-- A finite deletion list that excludes the rollup preserves its boundary. -/
theorem boundary_erase_list_refines (self : Address) (owners : List AccountAddress)
    (accounts : AccountMap) (keys : AccessScope) (absent : self ∉ owners)
    (ready : BoundaryReady self accounts keys) (safe : Safe (boundaryModel self accounts keys)) :
    BoundaryRefines self keys accounts (owners.foldl Batteries.RBMap.erase accounts) := by
  induction owners generalizing accounts with
  | nil => exact ⟨ready, safe, .initial⟩
  | cons owner rest ih =>
    have different : self ≠ owner := fun same => absent (same.symm ▸ List.mem_cons_self)
    have remaining : self ∉ rest := fun member => absent (List.mem_cons_of_mem _ member)
    have first := boundary_erase_refines self owner accounts keys different ready safe
    exact boundary_refines_trans first (ih _ remaining first.1 first.2.1)

/-- The transaction's tree fold preserves the rollup if its deletion set excludes the rollup. -/
theorem boundary_erase_set_refines (self : Address) (owners : Batteries.RBSet AccountAddress compare)
    (accounts : AccountMap) (keys : AccessScope) (absent : self ∉ owners)
    (ready : BoundaryReady self accounts keys) (safe : Safe (boundaryModel self accounts keys)) :
    BoundaryRefines self keys accounts (owners.1.foldl Batteries.RBMap.erase accounts) := by
  have excluded : self ∉ owners.toList := by
    intro member
    apply absent
    exact Batteries.RBSet.mem_iff_mem_toList.mpr ⟨self, member, by simp [compare, compareOfLessAndEq]⟩
  rw [Batteries.RBNode.foldl_eq_foldl_toList]
  exact boundary_erase_list_refines self owners.toList accounts keys excluded ready safe

end Rollup.EVM
