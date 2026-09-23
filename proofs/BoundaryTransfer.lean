import invariants.TreeBoundary
import proofs.BoundarySurplus
import proofs.WorldTransfers
import proofs.WorldCreationTransfers
import proofs.WorldNonce

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- Compose adjacent model traces at completed boundaries. -/
theorem boundary_refines_trans {self : Address} {keys : AccessScope} {before middle after : AccountMap}
    (first : BoundaryRefines self keys before middle) (second : BoundaryRefines self keys middle after) :
    BoundaryRefines self keys before after := by
  have combine : ∀ {a b c : Rollup.State}, CallTrace a b → CallTrace b c → CallTrace a c := by
    intro a b c left right
    induction right with
    | initial => exact left
    | next earlier step ih => exact .next ih step
  exact ⟨second.1, second.2.1, combine first.2.2 second.2.2⟩

/-- A protected code and storage frame with surplus ETH refines the boundary model. -/
theorem boundary_frame_refines {self : Address} {before after : AccountMap} {keys : AccessScope}
    (ready : BoundaryReady self before keys) (safe : Safe (boundaryModel self before keys))
    (frame : CodeStorageFrame self before after) (balances : EthFrame self before after) :
    BoundaryRefines self keys before after := by
  obtain ⟨next, effect⟩ := boundary_surplus_frame ready frame balances
  have trace := CallTrace.next CallTrace.initial effect
  exact ⟨next, callTrace_safe safe trace, trace⟩

/-- A funded call transfer cannot reduce rollup backing unless the rollup pays value. -/
theorem boundary_transfer_refines (self sender receiver : Address) (accounts : AccountMap)
    (value : UInt256) (keys : AccessScope) (ready : BoundaryReady self accounts keys)
    (safe : Safe (boundaryModel self accounts keys)) (senderSafe : self ≠ sender ∨ value = ⟨0⟩)
    (funds : value.toNat ≤ ethLedger accounts sender) :
    BoundaryRefines self keys accounts (sendEth receiver sender value true accounts) := by
  apply boundary_frame_refines ready safe (sendEth_accountStaticStateEq receiver sender value true accounts self)
  exact ⟨(sendEth_world accounts receiver sender value true funds (BoundaryReady.world ready)).le,
    sendEth_protected_balance accounts receiver sender self value true senderSafe funds (BoundaryReady.world ready)⟩

/-- A funded creation endowment preserves backing when its address differs from the sender. -/
theorem boundary_creation_transfer_refines (self sender receiver : Address) (accounts : AccountMap)
    (value : UInt256) (keys : AccessScope) (ready : BoundaryReady self accounts keys)
    (safe : Safe (boundaryModel self accounts keys)) (foreign : self ≠ sender)
    (different : receiver ≠ sender) (funds : value.toNat ≤ ethLedger accounts sender) :
    BoundaryRefines self keys accounts (sendEthCreate receiver sender value true accounts) := by
  apply boundary_frame_refines ready safe (sendEthCreate_static_state receiver sender value true accounts self)
  exact ⟨(sendEthCreate_world_ne accounts receiver sender value true different funds (BoundaryReady.world ready)).le,
    sendEthCreate_other_balance accounts receiver sender self value true different foreign funds (BoundaryReady.world ready)⟩

/-- The creation nonce update changes no rollup credit or ETH. -/
theorem boundary_nonce_refines (self sender : Address) (accounts : AccountMap) (keys : AccessScope)
    (ready : BoundaryReady self accounts keys) (safe : Safe (boundaryModel self accounts keys)) :
    BoundaryRefines self keys accounts (incrementNonce accounts sender) := by
  apply boundary_frame_refines ready safe (incrementNonce_storage accounts sender self)
  simp only [EthFrame, worldEth, incrementNonce_ethLedger, le_refl, and_self]

end Rollup.EVM
