import proofs.AccountMapValues
import proofs.BoundaryTransfer

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- Clear transient storage exactly as the transaction finalizer does. -/
def resetTransientStorage (accounts : AccountMap) : AccountMap :=
  mapAccountValues accounts (fun account => { account with tstorage := ∅ })

/-- Transient reset preserves account presence and all fields except transient storage. -/
theorem reset_transient_find (accounts : AccountMap) (owner : AccountAddress) :
    (resetTransientStorage accounts).find? owner =
      (accounts.find? owner).map (fun account => { account with tstorage := ∅ }) :=
  map_account_values_find accounts _ owner

/-- Transient reset preserves each account's ETH balance. -/
theorem reset_transient_ethLedger (accounts : AccountMap) :
    ethLedger (resetTransientStorage accounts) = ethLedger accounts := by
  funext owner
  simp only [ethLedger, Batteries.RBMap.findD, reset_transient_find]
  cases accounts.find? owner <;> rfl

/-- Transient reset preserves every persistent storage read. -/
theorem reset_transient_read (accounts : AccountMap) (self : Address) (slot : UInt256) :
    readWord (accountView self (resetTransientStorage accounts)) self slot =
      readWord (accountView self accounts) self slot := by
  simp only [readWord_default, accountView, Batteries.RBMap.findD, reset_transient_find]
  cases accounts.find? self <;> rfl

/-- Transient reset preserves the complete rollup accounting model. -/
theorem reset_transient_model (accounts : AccountMap) (self : Address) (keys : AccessScope) :
    boundaryModel self (resetTransientStorage accounts) keys = boundaryModel self accounts keys := by
  have reads := reset_transient_read accounts self
  have pending : pendingLedger (accountView self (resetTransientStorage accounts)) self keys =
      pendingLedger (accountView self accounts) self keys := by
    funext owner
    simp only [pendingLedger, reads]
  have claims : claimLedger (accountView self (resetTransientStorage accounts)) self keys =
      claimLedger (accountView self accounts) self keys := by
    funext owner
    simp only [claimLedger, reads]
  have balance : ((accountView self (resetTransientStorage accounts)).lookupAccount self).elim
      (⟨0⟩ : UInt256) (·.balance) =
      ((accountView self accounts).lookupAccount self).elim (⟨0⟩ : UInt256) (·.balance) := by
    simp only [accountView, Ethereum.State.lookupAccount, reset_transient_find]
    cases accounts.find? self <;> rfl
  simp only [boundaryModel, project, pending, claims, reads, balance]

/-- Transient reset preserves all conditions required at a rollup boundary. -/
theorem reset_transient_ready (accounts : AccountMap) (self : Address) (keys : AccessScope)
    (ready : BoundaryReady self accounts keys) : BoundaryReady self (resetTransientStorage accounts) keys := by
  refine ⟨⟨rfl, ?_⟩, ?_, ⟨ready.2.2.1.1, ready.2.2.1.2.1, ?_⟩, ?_⟩
  · have code := ready.1.2
    change ((resetTransientStorage accounts).find? self).map (·.code) = some runtimeBytecode
    change (accounts.find? self).map (·.code) = some runtimeBytecode at code
    rw [reset_transient_find]
    cases found : accounts.find? self <;>
      simpa only [found, Option.map_none, Option.map_some] using code
  · apply (worldBounded_iff_worldEth (accountView self (resetTransientStorage accounts))).mpr
    simpa only [accountView, worldEth, reset_transient_ethLedger] using BoundaryReady.world ready
  · intro slot outside
    rw [reset_transient_read]
    exact ready.2.2.1.2.2 slot outside
  · rw [reset_transient_read]
    exact ready.2.2.2

/-- The transaction's transient reset contributes no model state change. -/
theorem reset_transient_refines (accounts : AccountMap) (self : Address) (keys : AccessScope)
    (ready : BoundaryReady self accounts keys) (safe : Safe (boundaryModel self accounts keys)) :
    BoundaryRefines self keys accounts (resetTransientStorage accounts) := by
  refine ⟨reset_transient_ready accounts self keys ready, ?_, ?_⟩
  · rwa [reset_transient_model]
  · rw [reset_transient_model]
    exact .initial

end Rollup.EVM
