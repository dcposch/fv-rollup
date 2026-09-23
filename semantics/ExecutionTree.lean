import semantics.ActivePrefix
import semantics.CallScope

open Ethereum Ethereum.EVM

namespace Rollup.EVM

mutual
  /-- Record each actual instruction and each nested code execution. -/
  inductive FrameRun : Nat → Array UInt256 → Ethereum.State →
      Except ExecutionException (ExecutionResult Ethereum.State) → Type where
    | exhausted (jumps : Array UInt256) (start : Ethereum.State) :
        FrameRun 0 jumps start (.error .OutOfFuel)
    | failed {fuel jumps start error} (children : InstructionChildren jumps start)
        (executed : Xstep jumps start = .error error) :
        FrameRun (fuel + 1) jumps start (.error error)
    | returned {fuel jumps start after output} (children : InstructionChildren jumps start)
        (executed : Xstep jumps start = .ok (after, some (.success, output))) :
        FrameRun (fuel + 1) jumps start (.ok (.success after output))
    | reverted {fuel jumps start after output} (children : InstructionChildren jumps start)
        (executed : Xstep jumps start = .ok (after, some (.revert, output))) :
        FrameRun (fuel + 1) jumps start (.ok (.revert after.machineState.gasAvailable.toUInt256 output))
    | continued {fuel jumps start after result} (children : InstructionChildren jumps start)
        (executed : Xstep jumps start = .ok (after, none))
        (rest : FrameRun fuel jumps { after with executionEnv.depth := start.executionEnv.depth } result) :
        FrameRun (fuel + 1) jumps start result

  /-- Record the child selected by the instruction guards, including failed child executions. -/
  inductive InstructionChildren : Array UInt256 → Ethereum.State → Type where
    | none {jumps start}
        (noCall : ∀ child, ¬ ChildCallEntry jumps start child)
        (noCreation : ∀ child, ¬ ChildCreationEntry jumps start child) :
        InstructionChildren jumps start
    | call {jumps start child result} (entered : ChildCallEntry jumps start child)
        (run : FrameRun (child.machineState.gasAvailable.toNat + 1)
          (D_J child.executionEnv.code 0) child result) : InstructionChildren jumps start
    | creation {jumps start child result} (entered : ChildCreationEntry jumps start child)
        (run : FrameRun (child.machineState.gasAvailable.toNat + 1)
          (D_J child.executionEnv.code 0) child result) : InstructionChildren jumps start
end

/-- Collect calldata keys for executions in the rollup's storage context. -/
def frameCalldataScope (self : Address) (state : Ethereum.State) : AccessScope :=
  if state.executionEnv.codeOwner = self then calldataScope state.executionEnv else ∅

mutual
  def FrameRun.nestedScope (self : Address) :
      {fuel : Nat} → {jumps : Array UInt256} → {start : Ethereum.State} →
      {result : Except ExecutionException (ExecutionResult Ethereum.State)} →
      FrameRun fuel jumps start result → AccessScope
    | _, _, _, _, .exhausted _ _ => ∅
    | _, _, _, _, .failed children _ => children.scope self
    | _, _, _, _, .returned children _ => children.scope self
    | _, _, _, _, .reverted children _ => children.scope self
    | _, _, _, _, .continued children _ rest => children.scope self ∪ rest.nestedScope self

  def InstructionChildren.scope (self : Address) :
      {jumps : Array UInt256} → {start : Ethereum.State} → InstructionChildren jumps start → AccessScope
    | _, _, .none _ _ => ∅
    | _, _, @InstructionChildren.call _ _ child _ _ run =>
        frameCalldataScope self child ∪ run.nestedScope self
    | _, _, @InstructionChildren.creation _ _ child _ _ run =>
        frameCalldataScope self child ∪ run.nestedScope self
end

/-- The finite key set includes this frame and every nested frame, even under a reverted ancestor. -/
def FrameRun.scope {fuel jumps start result} (run : FrameRun fuel jumps start result)
    (self : Address) : AccessScope := frameCalldataScope self start ∪ run.nestedScope self

end Rollup.EVM
