import proofs.DepositEntry
import proofs.generated.KeccakDeposit

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Rollup.EVM

theorem deposit_selector_bytes :
    selectorOf contract.transitions[0]! = ⟨#[243, 64, 250, 1]⟩ := by
  unfold selectorOf
  have signature : transitionSigStr contract.transitions[0]! = "deposit(address)" := by
    change printSignature ⟨"deposit", [.elem .address]⟩ = _
    simp only [printSignature, List.map_cons, List.map_nil, abiToSigStr, elemToSigStr]
    decide +kernel
  rw [signature, deposit_selector_hash]
  decide +kernel

theorem deposit_selector_match (I : ExecutionEnv) (length : 4 ≤ I.calldata.size)
    (selector : solcSelectorWord I = ⟨0xf340fa01⟩) :
    ((⟨#[243, 64, 250, 1]⟩ : ByteArray) == I.calldata.extract 0 4) = true := by
  have comparison := evmSelectorDecode length 243 64 250 1 ⟨0xf340fa01⟩ (by decide)
  change UInt256.eq ⟨0xf340fa01⟩ (solcSelectorWord I) = _ at comparison
  rw [selector, u256_eq_refl] at comparison
  by_contra mismatch
  have noMatch := Bool.eq_false_of_not_eq_true mismatch
  rw [noMatch] at comparison
  exact (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) comparison

/-- The compiled deposit selector selects the source deposit function. -/
theorem deposit_selector_dispatch (I : ExecutionEnv) (length : 4 ≤ I.calldata.size)
    (selector : solcSelectorWord I = ⟨0xf340fa01⟩) :
    dispatchMsg contract I.calldata = some contract.transitions[0]! := by
  rw [dispatchMsg_eq_dispatchList contract I.calldata rfl rfl]
  change dispatchList (contract.transitions[0]! :: contract.transitions.tail) I.calldata = _
  rw [dispatchList_cons, deposit_selector_bytes,
    if_pos (deposit_selector_match I length selector)]

/-- The pinned deposit entry matches the source, including rejection paths. -/
theorem deposit_correct {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (code : I.code = runtimeBytecode) (writable : I.perm = true)
    (length : 4 ≤ I.calldata.size) (bounded : I.calldata.size < UInt256.size)
    (selector : solcSelectorWord I = ⟨0xf340fa01⟩)
    (maps : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I :=
  deposit_equivalence_for code writable bounded selector
    (deposit_selector_dispatch I length selector) maps

end Rollup.EVM
