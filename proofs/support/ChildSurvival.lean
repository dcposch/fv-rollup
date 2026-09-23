import proofs.support.AccountSurvival

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- Each actual child preserves account survival from its entry conditions. -/
def ChildFramesSurvive (self : Address) (jumps : Array UInt256) (before : Ethereum.State) : Prop :=
  ∀ child, (ChildCallEntry jumps before child ∨ ChildCreationEntry jumps before child) →
    StateSurvives self child → FrameResultSurvives self
      (X (child.machineState.gasAvailable.toNat + 1) (D_J child.executionEnv.code 0) child)

/-- The recorded child supplies its survival induction hypothesis. -/
def InstructionChildren.survives {jumps start} (children : InstructionChildren jumps start) (self : Address) : Prop :=
  match children with
  | .none _ _ => True
  | @InstructionChildren.call _ _ child result _ _ => StateSurvives self child → FrameResultSurvives self result
  | @InstructionChildren.creation _ _ child result _ _ => StateSurvives self child → FrameResultSurvives self result

end Rollup.EVM
