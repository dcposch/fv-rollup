import semantics.ExecutionRecord
import proofs.TreeBoundary
import proofs.TreeCoverage
import semantics.recording.ExecutionTreeComplete

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- A finite scope containing the execution's collected keys covers all nested root entries. -/
theorem execution_record_covered (fuel : Nat) (jumps : Array UInt256) (start : Ethereum.State)
    (self : Address) (keys : AccessScope)
    (scope : (executionRecord fuel jumps start).scope self ⊆ keys) :
    (executionRecord fuel jumps start).covered self keys :=
  frame_run_covered_of_scope _ self keys scope

/-- Actual foreign execution refines the boundary with scope collected from its complete record. -/
theorem foreign_execution_refines (fuel : Nat) (jumps : Array UInt256) (start : Ethereum.State)
    (self : Address) (keys : AccessScope)
    (ordinary : self ∉ π) (foreign : self ≠ start.executionEnv.codeOwner)
    (ready : BoundaryReady self start.accountMap keys)
    (safe : Safe (boundaryModel self start.accountMap keys))
    (scope : (executionRecord fuel jumps start).scope self ⊆ keys) :
    FrameResultRefines self keys start.accountMap (X fuel jumps start) :=
  frame_run_boundary _ self keys ordinary foreign ready safe
    (execution_record_covered fuel jumps start self keys scope)

end Rollup.EVM
