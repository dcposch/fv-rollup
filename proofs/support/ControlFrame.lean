import proofs.generated.ControlPaths

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- A concrete runtime state represented by the checked control-flow table. -/
def ControlFrameReady (state : Ethereum.State) : Prop :=
  state.executionEnv.code = runtimeBytecode ∧
    ∃ cursor ∈ controlPaths, cursor.denotes state

end Rollup.EVM
