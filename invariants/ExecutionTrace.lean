import semantics.ExecutionTrace
import invariants.Invariants

open Ethereum Ethereum.EVM Solm

namespace Rollup.EVM

/-- Target for completed boundaries. In-flight payment claims are separate. -/
def CompletedTraceCorrect : Prop :=
  ∀ self start events after keys,
    self ∉ π → BoundaryReady self start keys → Safe (boundaryModel self start keys) →
    ExecutionTrace self start events after → (∀ event ∈ events, event.covered keys) →
    BoundaryReady self after keys ∧ Safe (boundaryModel self after keys) ∧
      CallTrace (boundaryModel self start keys) (boundaryModel self after keys) ∧
      ∀ event ∈ events, event.refined keys

end Rollup.EVM
