import semantics.Storage

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- A finite prefix that has not halted, in one EVM execution frame. -/
inductive ContinuingPrefix (jumps : Array UInt256) (start : Ethereum.State) : Ethereum.State → Prop where
  | initial : ContinuingPrefix jumps start start
  | next {before after} : ContinuingPrefix jumps start before →
      Xstep jumps before = .ok (after, none) →
      ContinuingPrefix jumps start { after with executionEnv.depth := before.executionEnv.depth }

/-- Observe a frame before its next instruction or after one completed instruction. -/
inductive InstructionPrefix (jumps : Array UInt256) (start : Ethereum.State) : Ethereum.State → Prop where
  | current {state} : ContinuingPrefix jumps start state → InstructionPrefix jumps start state
  | afterStep {before after ret} : ContinuingPrefix jumps start before →
      Xstep jumps before = .ok (after, ret) → InstructionPrefix jumps start after

/-- Include the reserved payment while the receiver executes. -/
def inFlightProjection (state : Ethereum.State) (self : Address) (keys : AccessScope)
    (payment : Payment) : Rollup.State :=
  { project state self keys with payment := some payment }

end Rollup.EVM
