import proofs.DeploymentResult
import proofs.Boundary
import proofs.WorldStorage

open Ethereum Ethereum.EVM Reasoning.Theory

namespace Rollup.EVM

/-- Creation starts with the target's fresh storage. -/
theorem deployment_initial_storage (d : Deployment) (code : ByteArray) (fresh : d.fresh code) :
    ((d.initialAccounts code).findD (d.address code) default).storage = default := by
  unfold Deployment.initialAccounts
  cases found : d.accounts.find? d.sender with
  | none => exact fresh.2.2
  | some account =>
    simp only [Batteries.RBMap.findD, accountMap_find_insert_self, Option.getD_some]
    exact fresh.2.2

/-- A present sender creates the target account before constructor execution. -/
theorem deployment_initial_present (d : Deployment) (code : ByteArray)
    (present : (d.accounts.find? d.sender).isSome) :
    ((d.initialAccounts code).find? (d.address code)).isSome := by
  obtain ⟨sender, found⟩ := Option.isSome_iff_exists.mp present
  simp only [Deployment.initialAccounts, found, accountMap_find_insert_self, Option.isSome_some]

/-- Every storage read is zero at fresh constructor entry. -/
theorem deployment_initial_read (d : Deployment) (code : ByteArray) (fresh : d.fresh code)
    (slot : UInt256) :
    readWord (accountView (d.address code) (d.initialAccounts code)) (d.address code) slot = ⟨0⟩ := by
  rw [readWord_default]
  change ((d.initialAccounts code).findD (d.address code) default).storage.findD slot ⟨0⟩ = ⟨0⟩
  rw [deployment_initial_storage d code fresh]
  rfl

end Rollup.EVM
