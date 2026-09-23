import invariants.TreeBoundary

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- The induction hypothesis for each foreign child of one instruction. -/
def ChildFramesRefine (self : Address) (keys : AccessScope) (jumps : Array UInt256)
    (before : Ethereum.State) : Prop :=
  ∀ child, (ChildCallEntry jumps before child ∨ ChildCreationEntry jumps before child) →
    self ≠ child.executionEnv.codeOwner →
    BoundaryReady self child.accountMap keys → Safe (boundaryModel self child.accountMap keys) →
    FrameResultRefines self keys child.accountMap
      (X (child.machineState.gasAvailable.toNat + 1) (D_J child.executionEnv.code 0) child)

/-- The recorded child supplies the induction hypothesis for its result. -/
def InstructionChildren.refines {jumps start} (children : InstructionChildren jumps start)
    (self : Address) (keys : AccessScope) : Prop :=
  match children with
  | .none _ _ => True
  | @InstructionChildren.call _ _ child result _ _ =>
      self ≠ child.executionEnv.codeOwner →
      BoundaryReady self child.accountMap keys → Safe (boundaryModel self child.accountMap keys) →
      FrameResultRefines self keys child.accountMap result
  | @InstructionChildren.creation _ _ child result _ _ =>
      self ≠ child.executionEnv.codeOwner →
      BoundaryReady self child.accountMap keys → Safe (boundaryModel self child.accountMap keys) →
      FrameResultRefines self keys child.accountMap result

end Rollup.EVM
