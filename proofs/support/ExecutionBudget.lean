import proofs.support.ChildBoundary

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- A successful frame cannot increase total ETH. Its caller rolls back other outcomes. -/
def FrameResultBudget (before : AccountMap) :
    Except ExecutionException (ExecutionResult Ethereum.State) → Prop
  | .ok (.success after _) => total (fun owner => (after.accountMap.findD owner default).balance.toNat) ≤
      total (fun owner => (before.findD owner default).balance.toNat)
  | .ok (.revert _ _) => True
  | .error _ => True

/-- Each foreign child preserves the world budget under the carried rollup conditions. -/
def ChildFramesBudget (self : Address) (keys : AccessScope) (jumps : Array UInt256)
    (before : Ethereum.State) : Prop :=
  ∀ child, (ChildCallEntry jumps before child ∨ ChildCreationEntry jumps before child) →
    self ≠ child.executionEnv.codeOwner →
    BoundaryReady self child.accountMap keys → Safe (boundaryModel self child.accountMap keys) →
    FrameResultBudget child.accountMap
      (X (child.machineState.gasAvailable.toNat + 1) (D_J child.executionEnv.code 0) child)

/-- The recorded child supplies the budget induction hypothesis. -/
def InstructionChildren.budget {jumps start} (children : InstructionChildren jumps start)
    (self : Address) (keys : AccessScope) : Prop :=
  match children with
  | .none _ _ => True
  | @InstructionChildren.call _ _ child result _ _ =>
      self ≠ child.executionEnv.codeOwner →
      BoundaryReady self child.accountMap keys → Safe (boundaryModel self child.accountMap keys) →
      FrameResultBudget child.accountMap result
  | @InstructionChildren.creation _ _ child result _ _ =>
      self ≠ child.executionEnv.codeOwner →
      BoundaryReady self child.accountMap keys → Safe (boundaryModel self child.accountMap keys) →
      FrameResultBudget child.accountMap result

end Rollup.EVM
