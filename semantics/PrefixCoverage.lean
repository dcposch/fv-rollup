import semantics.ExecutionRecord
import semantics.ExecutionPrefix

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- Record the child executions of one actual instruction. -/
noncomputable def instructionRecord (jumps : Array UInt256) (state : Ethereum.State) :
    InstructionChildren jumps state := by
  have run := executionRecord 1 jumps state
  generalize resultEq : X 1 jumps state = result at run
  cases run with
  | failed children _ => exact children
  | returned children _ => exact children
  | reverted children _ => exact children
  | continued children _ _ => exact children

/-- A continuing prefix with finite coverage of its actual child records. -/
inductive CoveredPrefix (self : Address) (keys : AccessScope) (jumps : Array UInt256)
    (start : Ethereum.State) : Ethereum.State → Prop where
  | initial : CoveredPrefix self keys jumps start start
  | next {before after} : CoveredPrefix self keys jumps start before →
    (instructionRecord jumps before).scope self ⊆ keys →
    Xstep jumps before = .ok (after, none) →
    CoveredPrefix self keys jumps start { after with executionEnv.depth := before.executionEnv.depth }

end Rollup.EVM
