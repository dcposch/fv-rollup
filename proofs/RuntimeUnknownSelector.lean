import proofs.RuntimeBytecode

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Rollup.EVM

def runtimeSelectors : List UInt256 :=
  [⟨0x5c1bba38⟩, ⟨0x88af9950⟩, ⟨0x9588eca2⟩, ⟨0xba873065⟩,
   ⟨0xbb3ef682⟩, ⟨0xc9503fe2⟩, ⟨0xeb3349b9⟩, ⟨0xf340fa01⟩, ⟨0xf3f43703⟩]

/-- Unknown selectors revert or run out of gas. -/
theorem runtime_unknown_selector {cA gh bl σ σ₀ A I} {g : Sat256}
    (code : I.code = runtimeBytecode) (bounded : I.calldata.size < UInt256.size)
    (unknown : solcSelectorWord I ∉ runtimeSelectors) :
    RDrev runtimeBytecode g (initState cA gh bl σ σ₀ g A I) := by
  by_cases length : 4 ≤ I.calldata.size
  · have mismatch (word : UInt256) (member : word ∈ runtimeSelectors) :
        UInt256.eq word (solcSelectorWord I) = ⟨0⟩ := by
      apply u256_eq_of_ne
      intro same
      exact unknown (same ▸ member)
    obtain ⟨_, _, loaded⟩ := runtime_selector (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (g := g) code length bounded
    have compared := runtime_run loaded with [dup1, push4 ⟨0xbb3ef682⟩, gt, push2 ⟨87⟩]
    by_cases right : UInt256.gt ⟨0xbb3ef682⟩ (solcSelectorWord I) = ⟨0⟩
    · have split := runtime_run compared with [jumpiNT right]
      have first := runtime_run split with [dup1, push4 ⟨0xbb3ef682⟩, eq, push2 ⟨284⟩,
        jumpiNT (mismatch _ (by decide +kernel))]
      have second := runtime_run first with [dup1, push4 ⟨0xc9503fe2⟩, eq, push2 ⟨315⟩,
        jumpiNT (mismatch _ (by decide +kernel))]
      have third := runtime_run second with [dup1, push4 ⟨0xeb3349b9⟩, eq, push2 ⟨336⟩,
        jumpiNT (mismatch _ (by decide +kernel))]
      have fourth := runtime_run third with [dup1, push4 ⟨0xf340fa01⟩, eq, push2 ⟨379⟩,
        jumpiNT (mismatch _ (by decide +kernel))]
      have rejected := runtime_run fourth with [dup1, push4 ⟨0xf3f43703⟩, eq, push2 ⟨398⟩,
        jumpiNT (mismatch _ (by decide +kernel)), push0, dup1]
      exact rejected.rev 0 (by decide +kernel)
        (fun s _ stack => memExpRevert0 s stack) (by evm_ov)
    · have split := runtime_run compared with [
        jumpiT right (jumpScan_valid runtimeBytecode 87 140 (by decide +kernel)), jumpdest]
      have first := runtime_run split with [dup1, push4 ⟨0x5c1bba38⟩, eq, push2 ⟨136⟩,
        jumpiNT (mismatch _ (by decide +kernel))]
      have second := runtime_run first with [dup1, push4 ⟨0x88af9950⟩, eq, push2 ⟨195⟩,
        jumpiNT (mismatch _ (by decide +kernel))]
      have third := runtime_run second with [dup1, push4 ⟨0x9588eca2⟩, eq, push2 ⟨228⟩,
        jumpiNT (mismatch _ (by decide +kernel))]
      have rejected := runtime_run third with [dup1, push4 ⟨0xba873065⟩, eq, push2 ⟨263⟩,
        jumpiNT (mismatch _ (by decide +kernel)), jumpdest, push0, dup1]
      exact rejected.rev 0 (by decide +kernel)
        (fun s _ stack => memExpRevert0 s stack) (by evm_ov)
  · exact runtime_short_calldata code (by omega)

/-- Every accepted call has a known selector. -/
theorem runtime_success_selector {cA gh bl σ σ₀ A I} {g : Sat256}
    {cA' σ' gas substate output} (code : I.code = runtimeBytecode)
    (bounded : I.calldata.size < UInt256.size)
    (success : Ξ cA gh bl σ σ₀ g.toUInt256 A I = .ok (.success (cA', σ', gas, substate) output)) :
    solcSelectorWord I ∈ runtimeSelectors := by
  by_contra unknown
  have rejected := runtime_unknown_selector (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) code bounded unknown
  rcases rejected.xiResult code with failed | ⟨gas', data, actual⟩
  · rw [success] at failed
    cases failed
  · rw [success] at actual
    cases actual

end Rollup.EVM
