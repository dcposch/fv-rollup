import proofs.InstructionSurvival

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- Complete execution preserves an existing account's code and lifecycle conditions. -/
theorem frame_run_survives {fuel jumps start result} (run : FrameRun fuel jumps start result) :
    ∀ self, StateSurvives self start → FrameResultSurvives self result := by
  refine FrameRun.rec
    (motive_1 := fun _ _ start result _ =>
      ∀ self, StateSurvives self start → FrameResultSurvives self result)
    (motive_2 := fun _ _ children => ∀ self, children.survives self)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ run
  · intro jumps start self initial
    trivial
  · intro fuel jumps start error children executed ih self initial
    trivial
  · intro fuel jumps start after output children executed ih self initial
    exact instruction_tree_survives children initial (ih self) executed
  · intro fuel jumps start after output children executed ih self initial
    trivial
  · intro fuel jumps start after result children executed rest childIH restIH self initial
    have first := instruction_tree_survives children initial (childIH self) executed
    exact restIH self first
  · intro jumps start noCall noCreation self
    trivial
  · intro jumps start child result entered run ih self
    exact ih self
  · intro jumps start child result entered run ih self
    exact ih self

end Rollup.EVM
