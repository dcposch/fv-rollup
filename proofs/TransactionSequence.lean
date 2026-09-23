import semantics.TransactionSequence
import proofs.TransactionSurvival
import proofs.DeploymentBoundary
import invariants.TraceObligations

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- Collect fixed slots and nested calldata keys from all transactions. -/
noncomputable def transactionSequenceScope (self : Address) : List TransactionEvent → AccessScope
  | [] => fixedKeys
  | event :: rest => event.scope self ∪ transactionSequenceScope self rest

/-- The collected transaction scope includes all fixed slots. -/
theorem transaction_sequence_scope_fixed (self : Address) (events : List TransactionEvent) :
    fixedKeys ⊆ transactionSequenceScope self events := by
  induction events with
  | nil => exact Finset.Subset.refl _
  | cons event rest ih => exact Finset.Subset.trans ih Finset.subset_union_right

/-- The collected scope covers each transaction and all its nested frames. -/
theorem transaction_sequence_scope_covered (self : Address) (events : List TransactionEvent) :
    ∀ event ∈ events, event.scope self ⊆ transactionSequenceScope self events := by
  induction events with
  | nil => simp
  | cons first rest ih =>
    intro event member
    rcases List.mem_cons.mp member with rfl | member
    · exact Finset.subset_union_left
    · exact Finset.Subset.trans (ih event member) Finset.subset_union_right

/-- Complete transactions compose through fees, nested execution, and account cleanup. -/
theorem transaction_sequence_refines {self start events after keys}
    (ordinary : self ∉ π) (ready : BoundaryReady self start keys)
    (safe : Safe (boundaryModel self start keys))
    (trace : TransactionSequence self start events after)
    (covered : ∀ event ∈ events, event.scope self ⊆ keys) :
    BoundaryRefines self keys start after := by
  induction trace with
  | initial => exact ⟨ready, safe, .initial⟩
  | @next events event earlier admissible executed ih =>
    have previous : ∀ item ∈ events, item.scope self ⊆ keys := by
      intro item member
      exact covered item (List.mem_append_left _ member)
    have current : event.scope self ⊆ keys := covered event (by simp)
    have first := ih previous
    obtain ⟨foreign, account, found, nonce, price, funds, bounded⟩ := admissible
    have last := transaction_boundary event.before event.after event.baseFee event.header event.genesis
      event.blocks event.transaction event.sender self account keys event.substate event.accepted event.gas
      found ordinary foreign nonce price funds bounded first.1 first.2.1 current executed
    exact boundary_refines_trans first last

/-- Deployment and complete transactions refine the rollup model with scope from actual execution. -/
theorem deployed_transaction_sequence_correct
    (deployment : Deployment) (sequencer : Address) (root : Root)
    (self : Address) (created : Batteries.RBSet AccountAddress compare)
    (accounts : AccountMap) (gas : UInt256) (substate : Substate) (data : ByteArray)
    (events : List TransactionEvent) (after : AccountMap)
    (distinct : NoAlias (transactionSequenceScope self events)) (nonzero : sequencer ≠ 0)
    (fresh : deployment.fresh (deploymentCode sequencer root))
    (present : (deployment.accounts.find? deployment.sender).isSome)
    (world : WorldBounded (accountView self deployment.accounts)) (ordinary : self ∉ π)
    (deployed : deployment.run (deploymentCode sequencer root) =
      (self, created, accounts, gas, substate, true, data))
    (trace : TransactionSequence self accounts events after) :
    let keys := transactionSequenceScope self events
    BoundaryReady self after keys ∧ Safe (boundaryModel self after keys) ∧
      CallTrace (initial self sequencer root (deployment.accounts.findD self default).balance.toNat)
        (boundaryModel self after keys) := by
  let keys := transactionSequenceScope self events
  have bounded := (worldBounded_iff_worldEth (accountView self deployment.accounts)).mp world
  obtain ⟨ready, model, safe⟩ := deployment_refines_scope deployment sequencer root keys
    (transaction_sequence_scope_fixed self events) distinct nonzero fresh present bounded deployed
  have effect := transaction_sequence_refines ordinary ready safe trace
    (transaction_sequence_scope_covered self events)
  refine ⟨effect.1, effect.2.1, ?_⟩
  have committed := effect.2.2
  rw [model] at committed
  exact committed

end Rollup.EVM
