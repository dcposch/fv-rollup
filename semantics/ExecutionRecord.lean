import semantics.recording.ExecutionTreeComplete

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- Select the complete record whose existence follows from actual EVM execution. -/
noncomputable def executionRecord (fuel : Nat) (jumps : Array UInt256) (start : Ethereum.State) :
    FrameRun fuel jumps start (X fuel jumps start) :=
  Classical.choice (frame_run_complete fuel jumps start)

end Rollup.EVM
