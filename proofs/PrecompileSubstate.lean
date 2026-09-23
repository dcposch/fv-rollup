import Ethereum.Theory.StaticStorage

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- Each modeled precompile preserves the transaction substate. -/
theorem precompile_substate (accounts : AccountMap) (gas : UInt256) (substate : Substate) (env : ExecutionEnv) :
    (Ξ_ECREC accounts gas substate env).2.2.1 = substate ∧
    (Ξ_SHA256 accounts gas substate env).2.2.1 = substate ∧
    (Ξ_RIP160 accounts gas substate env).2.2.1 = substate ∧
    (Ξ_ID accounts gas substate env).2.2.1 = substate ∧
    (Ξ_EXPMOD accounts gas substate env).2.2.1 = substate ∧
    (Ξ_BN_ADD accounts gas substate env).2.2.1 = substate ∧
    (Ξ_BN_MUL accounts gas substate env).2.2.1 = substate ∧
    (Ξ_SNARKV accounts gas substate env).2.2.1 = substate ∧
    (Ξ_BLAKE2_F accounts gas substate env).2.2.1 = substate ∧
    (Ξ_PointEval accounts gas substate env).2.2.1 = substate := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Ξ_ECREC]; split <;> simp
  · simp only [Ξ_SHA256]; split <;> simp
  · simp only [Ξ_RIP160]; split <;> simp
  · simp only [Ξ_ID]; split <;> simp
  · unfold Ξ_EXPMOD
    simp only
    repeat' (first | split | rfl)
  · simp only [Ξ_BN_ADD]
    repeat' (first | split | rfl)
  · simp only [Ξ_BN_MUL]
    repeat' (first | split | rfl)
  · simp only [Ξ_SNARKV]
    repeat' (first | split | rfl)
  · simp only [Ξ_BLAKE2_F]
    repeat' (first | split | rfl)
  · simp only [Ξ_PointEval]
    repeat' (first | split | rfl)

end Rollup.EVM
