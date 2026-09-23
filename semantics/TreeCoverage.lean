import semantics.ExecutionTree

namespace Rollup.EVM

mutual
  /-- Cover every root-context calldata read in this frame and its descendants. -/
  def FrameRun.covered {fuel jumps start result} (run : FrameRun fuel jumps start result)
      (self : Address) (keys : AccessScope) : Prop :=
    (start.executionEnv.codeOwner = self → CalldataCovered start keys) ∧
      match run with
      | .exhausted _ _ => True
      | .failed children _ => children.covered self keys
      | .returned children _ => children.covered self keys
      | .reverted children _ => children.covered self keys
      | .continued children _ rest => children.covered self keys ∧ rest.covered self keys

  def InstructionChildren.covered {jumps start} (children : InstructionChildren jumps start)
      (self : Address) (keys : AccessScope) : Prop :=
    match children with
    | .none _ _ => True
    | .call _ run => run.covered self keys
    | .creation _ run => run.covered self keys
end

end Rollup.EVM
