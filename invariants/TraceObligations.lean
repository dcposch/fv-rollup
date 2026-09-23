import invariants.ExecutionTrace
import semantics.DeploymentCode
import semantics.ExecutionTrace
import semantics.Deployment

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- Target for actual deployment followed by finite completed-call execution. -/
def DeployedBoundaryTraceCorrect : Prop :=
  ∀ (deployment : Deployment) (sequencer : Address) (root : Root)
    (keys : AccessScope) (self : Address) (created : Batteries.RBSet AccountAddress compare)
    (accounts : AccountMap) (gas : UInt256) (substate : Substate) (data : ByteArray)
    (events : List ExecutionEvent) (after : AccountMap),
    fixedKeys ⊆ keys → NoAlias keys → sequencer ≠ 0 →
    deployment.fresh (deploymentCode sequencer root) →
    (deployment.accounts.find? deployment.sender).isSome →
    WorldBounded (accountView self deployment.accounts) → self ∉ π →
    deployment.run (deploymentCode sequencer root) =
      (self, created, accounts, gas, substate, true, data) →
    ExecutionTrace self accounts events after → (∀ event ∈ events, event.covered keys) →
    BoundaryReady self after keys ∧ Safe (boundaryModel self after keys) ∧
      CallTrace (initial self sequencer root (deployment.accounts.findD self default).balance.toNat)
        (boundaryModel self after keys) ∧
      ∀ event ∈ events, event.refined keys

end Rollup.EVM
