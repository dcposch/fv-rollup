import semantics.Environment
import proofs.World
import proofs.Accounting
import Ethereum.Theory.AccountLocality

open Ethereum Ethereum.EVM Reasoning.Theory
open scoped BigOperators

namespace Rollup.EVM

def ethLedger (accounts : AccountMap) : Ledger :=
  fun owner => (accounts.findD owner default).balance.toNat

noncomputable def worldEth (accounts : AccountMap) : Nat := total (ethLedger accounts)

theorem ethLedger_lookup (accounts : AccountMap) (owner : Address) :
    ethLedger accounts owner = ((accounts.find? owner).elim (⟨0⟩ : UInt256) (·.balance)).toNat := by
  cases found : accounts.find? owner <;> simp [ethLedger, Batteries.RBMap.findD, found]
  rfl

theorem worldBounded_iff_worldEth (evm : Ethereum.State) :
    WorldBounded evm ↔ worldEth evm.accountMap < wordLimit := by
  simp only [WorldBounded, worldEth, total, ethLedger_lookup, Ethereum.State.lookupAccount]

theorem ethLedger_insert (accounts : AccountMap) (owner : Address) (account : Account) :
    ethLedger (accounts.insert owner account) =
      Function.update (ethLedger accounts) owner account.balance.toNat := by
  funext query
  by_cases same : query = owner
  · subst query
    simp [ethLedger, Batteries.RBMap.findD, accountMap_find_insert_self]
  · simp [ethLedger, Batteries.RBMap.findD, accountMap_find?_insert_ne _ _ _ _ same,
      Function.update_of_ne same]

/-- Replacing an account changes total ETH by its balance change. -/
theorem worldEth_insert (accounts : AccountMap) (owner : Address) (account : Account) :
    worldEth (accounts.insert owner account) + ethLedger accounts owner =
      worldEth accounts + account.balance.toNat := by
  classical
  simp only [worldEth, ethLedger_insert, total,
    Finset.sum_update_of_mem (Finset.mem_univ owner), Finset.sdiff_singleton_eq_erase]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ owner)]
  omega

/-- Two distinct account balances are bounded by total ETH. -/
theorem eth_pair_le_world (accounts : AccountMap) (first second : Address)
    (different : first ≠ second) :
    ethLedger accounts first + ethLedger accounts second ≤ worldEth accounts := by
  classical
  have part : ethLedger accounts first ≤
      ∑ owner ∈ (Finset.univ : Finset Address).erase second, ethLedger accounts owner :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _)
      (Finset.mem_erase.mpr ⟨different, Finset.mem_univ first⟩)
  have sum := Finset.sum_erase_add (Finset.univ : Finset Address) (ethLedger accounts)
    (Finset.mem_univ second)
  change _ = worldEth accounts at sum
  omega

/-- A funded transfer to a distinct account cannot overflow the recipient. -/
theorem funded_recipient_bound (accounts : AccountMap) (receiver sender : Address) (value : UInt256)
    (different : receiver ≠ sender)
    (funds : value.toNat ≤ ethLedger accounts sender)
    (world : worldEth accounts < wordLimit) :
    ethLedger accounts receiver + value.toNat < UInt256.size := by
  have pair := eth_pair_le_world accounts receiver sender different
  change worldEth accounts < UInt256.size at world
  omega

end Rollup.EVM
