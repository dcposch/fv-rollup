import semantics.Bytecode
import Ethereum.Theory.StaticStorage

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- A static call preserves the rollup code and both storage maps. -/
theorem static_call_preserves_rollup
    {blobVersionedHashes cA gh bl σ σ₀ A sender origin receiver code gas price value value'
      calldata depth header cA' σ' gas' A' accepted output}
    (self : AccountAddress) (before : Account)
    (present : σ.find? self = some before)
    (pinned : before.code = runtimeBytecode)
    (run : Θ blobVersionedHashes cA gh bl σ σ₀ A sender origin receiver code
      gas price value value' calldata depth header false =
      (cA', σ', gas', A', accepted, output)) :
    ∃ after, σ'.find? self = some after ∧ after.code = runtimeBytecode ∧
      after.storage = before.storage ∧ after.tstorage = before.tstorage := by
  have preserved := Theta_static_accountStaticStateEq run self
  cases found : σ'.find? self with
  | none =>
    simp only [Batteries.RBMap.findD, present, found, Option.getD_some,
      Option.getD_none] at preserved
    have nonempty : runtimeBytecode ≠ (default : Account).code := by decide +kernel
    exact False.elim (nonempty (pinned.symm.trans preserved.2.2))
  | some after =>
    simp only [Batteries.RBMap.findD, present, found, Option.getD_some] at preserved
    exact ⟨after, rfl, preserved.2.2.symm.trans pinned,
      preserved.1.symm, preserved.2.1.symm⟩

end Rollup.EVM
