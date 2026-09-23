import invariants.TraceObligations
import proofs.ExecutionTrace
import proofs.DeploymentBoundary
import proofs.TraceScope

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- Actual deployment and finite EVM execution refine the model without correctness premises. -/
theorem deployed_boundary_trace_correct : DeployedBoundaryTraceCorrect := by
  intro deployment sequencer root keys self created accounts gas substate data events after
    fixed distinct nonzero fresh present world ordinary deployed trace covered
  have bounded := (worldBounded_iff_worldEth (accountView self deployment.accounts)).mp world
  obtain ⟨ready, model, safe⟩ := deployment_refines_scope deployment sequencer root keys fixed
    distinct nonzero fresh present bounded deployed
  obtain ⟨finalReady, finalSafe, modelTrace, results⟩ :=
    completed_trace_correct self accounts events after keys ordinary ready safe trace covered
  rw [model] at modelTrace
  exact ⟨finalReady, finalSafe, modelTrace, results⟩

/-- Derive the root-call storage scope from the actual trace calldata. -/
theorem deployed_trace_from_calldata
    (deployment : Deployment) (sequencer : Address) (root : Root)
    (self : Address) (created : Batteries.RBSet AccountAddress compare)
    (accounts : AccountMap) (gas : UInt256) (substate : Substate) (data : ByteArray)
    (events : List ExecutionEvent) (after : AccountMap)
    (distinct : NoAlias (executionScope events)) (nonzero : sequencer ≠ 0)
    (fresh : deployment.fresh (deploymentCode sequencer root))
    (present : (deployment.accounts.find? deployment.sender).isSome)
    (world : WorldBounded (accountView self deployment.accounts)) (ordinary : self ∉ π)
    (deployed : deployment.run (deploymentCode sequencer root) =
      (self, created, accounts, gas, substate, true, data))
    (trace : ExecutionTrace self accounts events after) :
    let keys := executionScope events
    BoundaryReady self after keys ∧ Safe (boundaryModel self after keys) ∧
      CallTrace (initial self sequencer root (deployment.accounts.findD self default).balance.toNat)
        (boundaryModel self after keys) ∧
      ∀ event ∈ events, event.refined keys :=
  deployed_boundary_trace_correct deployment sequencer root (executionScope events) self
    created accounts gas substate data events after (execution_scope_fixed events) distinct
    nonzero fresh present world ordinary deployed trace (execution_scope_covered events)

end Rollup.EVM
