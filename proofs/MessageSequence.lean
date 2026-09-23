import proofs.support.MessageSequence
import proofs.SurroundingMessage
import proofs.DeploymentBoundary
import invariants.TraceObligations

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- Collect fixed slots and all nested root calldata keys from the actual message executions. -/
noncomputable def messageSequenceScope (self : Address) : List (MessageCall × MessageResult) → AccessScope
  | [] => fixedKeys
  | (call, _) :: rest => selectedMessageScope call self ∪ messageSequenceScope self rest

/-- The collected message scope includes every fixed storage slot. -/
theorem message_sequence_scope_fixed (self : Address) (events : List (MessageCall × MessageResult)) :
    fixedKeys ⊆ messageSequenceScope self events := by
  induction events with
  | nil => exact Finset.Subset.refl _
  | cons event rest ih => exact Finset.Subset.trans ih Finset.subset_union_right

/-- The collected scope covers each message and all its nested frames. -/
theorem message_sequence_scope_covered (self : Address) (events : List (MessageCall × MessageResult)) :
    ∀ event ∈ events, selectedMessageScope event.1 self ⊆ messageSequenceScope self events := by
  induction events with
  | nil => simp
  | cons first rest ih =>
    intro event member
    rcases List.mem_cons.mp member with rfl | member
    · exact Finset.subset_union_left
    · exact Finset.Subset.trans (ih event member) Finset.subset_union_right

/-- Complete messages compose regardless of their top-level receiver. -/
theorem message_sequence_refines {self start events after keys}
    (ordinary : self ∉ π) (ready : BoundaryReady self start keys)
    (safe : Safe (boundaryModel self start keys))
    (trace : MessageSequence self start events after)
    (covered : ∀ event ∈ events, selectedMessageScope event.1 self ⊆ keys) :
    BoundaryRefines self keys start after := by
  induction trace with
  | initial => exact ⟨ready, safe, .initial⟩
  | @next events call result earlier sender context bounded funds executed ih =>
    have previous : ∀ event ∈ events, selectedMessageScope event.1 self ⊆ keys := by
      intro event member
      exact covered event (List.mem_append_left _ member)
    have current : selectedMessageScope call self ⊆ keys := covered (call, result) (by simp)
    have first := ih previous
    have last := selected_message_refines call result executed ordinary sender context bounded
      first.1 first.2.1 funds current
    exact boundary_refines_trans first last

/-- Deployment and arbitrary complete messages refine the model with scope taken from execution. -/
theorem deployed_message_sequence_correct
    (deployment : Deployment) (sequencer : Address) (root : Root)
    (self : Address) (created : Batteries.RBSet AccountAddress compare)
    (accounts : AccountMap) (gas : UInt256) (substate : Substate) (data : ByteArray)
    (events : List (MessageCall × MessageResult)) (after : AccountMap)
    (distinct : NoAlias (messageSequenceScope self events)) (nonzero : sequencer ≠ 0)
    (fresh : deployment.fresh (deploymentCode sequencer root))
    (present : (deployment.accounts.find? deployment.sender).isSome)
    (world : WorldBounded (accountView self deployment.accounts)) (ordinary : self ∉ π)
    (deployed : deployment.run (deploymentCode sequencer root) =
      (self, created, accounts, gas, substate, true, data))
    (trace : MessageSequence self accounts events after) :
    let keys := messageSequenceScope self events
    BoundaryReady self after keys ∧ Safe (boundaryModel self after keys) ∧
      CallTrace (initial self sequencer root (deployment.accounts.findD self default).balance.toNat)
        (boundaryModel self after keys) := by
  let keys := messageSequenceScope self events
  have bounded := (worldBounded_iff_worldEth (accountView self deployment.accounts)).mp world
  obtain ⟨ready, model, safe⟩ := deployment_refines_scope deployment sequencer root keys
    (message_sequence_scope_fixed self events) distinct nonzero fresh present bounded deployed
  have effect := message_sequence_refines ordinary ready safe trace (message_sequence_scope_covered self events)
  refine ⟨effect.1, effect.2.1, ?_⟩
  have committed := effect.2.2
  rw [model] at committed
  exact committed

end Rollup.EVM
