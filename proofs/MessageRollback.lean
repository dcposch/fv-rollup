import proofs.MessageCall
import proofs.Boundary

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- Rejection restores the checkpoint for any selected code or precompile. -/
theorem theta_rejected_checkpoint
    {blobs cA gh bl accounts original substate sender origin receiver code gas price value contextValue
      calldata depth header writable cA' after gas' substate' output}
    (run : Θ blobs cA gh bl accounts original substate sender origin receiver code
      gas price value contextValue calldata depth header writable =
      (cA', after, gas', substate', false, output)) :
    after = accounts ∧ substate' = substate := by
  unfold Θ at run
  extract_lets at run
  simp only [Prod.mk.injEq] at run
  have failed := run.2.2.2.2.1
  split_ifs at failed with empty
  · simp only [empty, if_true] at run
    exact ⟨run.2.1.symm, run.2.2.2.1.symm⟩

end Rollup.EVM
