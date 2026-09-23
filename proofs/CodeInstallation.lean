import proofs.Boundary
import proofs.WorldStorage

open Ethereum Ethereum.EVM Reasoning.Theory

namespace Rollup.EVM

def installRuntime (accounts : AccountMap) (self : Address) : AccountMap :=
  accounts.insert self { accounts.findD self default with code := runtimeBytecode }

/-- Code installation preserves every ETH balance. -/
theorem installRuntime_ethLedger (accounts : AccountMap) (self : Address) :
    ethLedger (installRuntime accounts self) = ethLedger accounts :=
  ethLedger_insert_same_balance accounts self _ rfl

/-- Code installation preserves every rollup storage read. -/
theorem installRuntime_read (accounts : AccountMap) (self : Address) (slot : UInt256) :
    readWord (accountView self (installRuntime accounts self)) self slot =
      readWord (accountView self accounts) self slot := by
  simp only [readWord_default, accountView, installRuntime, Batteries.RBMap.findD,
    accountMap_find_insert_self, Option.getD_some]

/-- Code installation preserves the model state. -/
theorem installRuntime_project (accounts : AccountMap) (self : Address) (keys : AccessScope) :
    boundaryModel self (installRuntime accounts self) keys = boundaryModel self accounts keys := by
  have reads := installRuntime_read accounts self
  have pending : pendingLedger (accountView self (installRuntime accounts self)) self keys =
      pendingLedger (accountView self accounts) self keys := by
    funext owner
    simp only [pendingLedger, reads]
  have claims : claimLedger (accountView self (installRuntime accounts self)) self keys =
      claimLedger (accountView self accounts) self keys := by
    funext owner
    simp only [claimLedger, reads]
  have balance : ((accountView self (installRuntime accounts self)).lookupAccount self).elim
      (⟨0⟩ : UInt256) (·.balance) =
      ((accountView self accounts).lookupAccount self).elim (⟨0⟩ : UInt256) (·.balance) := by
    simp only [accountView, Ethereum.State.lookupAccount, installRuntime, accountMap_find_insert_self]
    cases found : accounts.find? self <;> simp [Batteries.RBMap.findD, found]
    rfl
  simp only [boundaryModel, project, pending, claims, reads, balance]

/-- Installing the runtime establishes code ownership and preserves boundary conditions. -/
theorem installRuntime_ready (accounts : AccountMap) (self : Address) (keys : AccessScope)
    (world : worldEth accounts < wordLimit)
    (ready : StorageReady (accountView self accounts) self keys)
    (unlocked : readWord (accountView self accounts) self ⟨6⟩ = ⟨0⟩) :
    BoundaryReady self (installRuntime accounts self) keys := by
  refine ⟨⟨rfl, ?_⟩, ?_, ⟨ready.1, ready.2.1, ?_⟩, ?_⟩
  · simp only [accountView, Ethereum.State.lookupAccount, installRuntime,
      accountMap_find_insert_self, Option.map_some]
  · apply (worldBounded_iff_worldEth (accountView self (installRuntime accounts self))).mpr
    change worldEth (installRuntime accounts self) < wordLimit
    simpa only [worldEth, installRuntime_ethLedger] using world
  · intro slot outside
    rw [installRuntime_read]
    exact ready.2.2 slot outside
  · rwa [installRuntime_read]

end Rollup.EVM
