import invariants.Invariants
import semantics.TreeCoverage
import semantics.Boundary
import semantics.Calls

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- A completed surrounding action preserves the rollup conditions and has a model trace. -/
def BoundaryRefines (self : Address) (keys : AccessScope) (before after : AccountMap) : Prop :=
  BoundaryReady self after keys ∧ Safe (boundaryModel self after keys) ∧
    CallTrace (boundaryModel self before keys) (boundaryModel self after keys)

/-- Successful foreign frames expose accounts; failed frames are rolled back by their caller. -/
def FrameResultRefines (self : Address) (keys : AccessScope) (before : AccountMap) :
    Except ExecutionException (ExecutionResult Ethereum.State) → Prop
  | .ok (.success after _) => BoundaryRefines self keys before after.accountMap
  | .ok (.revert _ _) => True
  | .error _ => True

/-- Full surrounding-frame target with a scope derived from every nested code execution. -/
def TreeBoundaryCorrect : Prop :=
  ∀ (self : Address) (keys : AccessScope) (fuel : Nat) (jumps : Array UInt256)
    (start : Ethereum.State) (result : Except ExecutionException (ExecutionResult Ethereum.State))
    (run : FrameRun fuel jumps start result),
    self ∉ π → self ≠ start.executionEnv.codeOwner →
    BoundaryReady self start.accountMap keys → Safe (boundaryModel self start.accountMap keys) →
    run.covered self keys → FrameResultRefines self keys start.accountMap result

end Rollup.EVM
