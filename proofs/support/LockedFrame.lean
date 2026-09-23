import proofs.generated.LockedPaths
import proofs.support.FrameCertificate

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- A locked runtime state whose counter and stack are in the checked table. -/
def LockedFrameReady (state : Ethereum.State) : Prop :=
  state.executionEnv.code = runtimeBytecode ∧ (state.sload ⟨6⟩).2 ≠ ⟨0⟩ ∧
    ∃ cursor ∈ lockedPaths, cursor.denotes state

end Rollup.EVM
