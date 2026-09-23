import semantics.ExecutionTree
import semantics.recording.ChildDepth

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- Every finite EVM run has a tree with all guarded child code executions. -/
theorem frame_run_complete (fuel : Nat) (jumps : Array UInt256) (start : Ethereum.State) :
    Nonempty (FrameRun fuel jumps start (X fuel jumps start)) := by
  classical
  generalize remainingEq : 1024 - start.executionEnv.depth.val = remaining
  induction remaining using Nat.strong_induction_on generalizing fuel jumps start with
  | h remaining deeper =>
    induction fuel generalizing start with
    | zero => simpa only [X] using (Nonempty.intro (FrameRun.exhausted jumps start))
    | succ fuel shorter =>
      have children : Nonempty (InstructionChildren jumps start) := by
        by_cases hasCall : ∃ child, ChildCallEntry jumps start child
        · obtain ⟨child, entered⟩ := hasCall
          obtain ⟨tree⟩ := deeper _ (by rw [← remainingEq]; exact child_call_remaining entered)
            (child.machineState.gasAvailable.toNat + 1) (D_J child.executionEnv.code 0) child rfl
          exact ⟨.call entered tree⟩
        · by_cases hasCreation : ∃ child, ChildCreationEntry jumps start child
          · obtain ⟨child, entered⟩ := hasCreation
            obtain ⟨tree⟩ := deeper _ (by rw [← remainingEq]; exact child_creation_remaining entered)
              (child.machineState.gasAvailable.toNat + 1) (D_J child.executionEnv.code 0) child rfl
            exact ⟨.creation entered tree⟩
          · exact ⟨.none (fun child entered => hasCall ⟨child, entered⟩)
              (fun child entered => hasCreation ⟨child, entered⟩)⟩
      obtain ⟨children⟩ := children
      cases executed : Xstep jumps start with
      | error error =>
        simpa only [X, executed, bind, Except.bind] using
          (Nonempty.intro (FrameRun.failed (fuel := fuel) children executed))
      | ok result =>
        rcases result with ⟨after, ret⟩
        cases ret with
        | none =>
          obtain ⟨rest⟩ := shorter (start := { after with executionEnv.depth := start.executionEnv.depth }) remainingEq
          simpa only [X, executed, bind, Except.bind] using
            (Nonempty.intro (FrameRun.continued children executed rest))
        | some halted =>
          rcases halted with ⟨cause, output⟩
          cases cause with
          | success =>
            simpa only [X, executed, bind, Except.bind] using
              (Nonempty.intro (FrameRun.returned (fuel := fuel) children executed))
          | revert =>
            simpa only [X, executed, bind, Except.bind] using
              (Nonempty.intro (FrameRun.reverted (fuel := fuel) children executed))

end Rollup.EVM
