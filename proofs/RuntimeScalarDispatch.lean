import proofs.RuntimeScalarGetter

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Rollup.EVM

/-- Each scalar selector reaches its getter entry with no account changes. -/
theorem scalar_getter_dispatch {cA gh bl σ σ₀ A I} {g : Sat256}
    (getter : ScalarGetter) (code : I.code = runtimeBytecode)
    (length : 4 ≤ I.calldata.size) (bounded : I.calldata.size < UInt256.size)
    (selector : solcSelectorWord I = scalarSelector getter) :
    ∃ k C, RD runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) (scalarEntry getter)
      [scalarSelector getter] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, loaded⟩ := runtime_selector (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) code length bounded
  rw [selector] at loaded
  cases getter with
  | stateRoot =>
    have split := runtime_run loaded with [dup1, push4 ⟨0xbb3ef682⟩, gt, push2 ⟨87⟩,
      jumpiT (by decide +kernel) (jumpScan_valid runtimeBytecode 87 140 (by decide +kernel)), jumpdest]
    have first := runtime_run split with [dup1, push4 ⟨0x5c1bba38⟩, eq, push2 ⟨136⟩,
      jumpiNT (by decide +kernel)]
    have second := runtime_run first with [dup1, push4 ⟨0x88af9950⟩, eq, push2 ⟨195⟩,
      jumpiNT (by decide +kernel)]
    exact ⟨_, _, runtime_run second with [dup1, push4 ⟨0x9588eca2⟩, eq, push2 ⟨228⟩,
      jumpiT (by decide +kernel) (jumpScan_valid runtimeBytecode 228 350 (by decide +kernel))]⟩
  | batchNumber =>
    have split := runtime_run loaded with [dup1, push4 ⟨0xbb3ef682⟩, gt, push2 ⟨87⟩,
      jumpiT (by decide +kernel) (jumpScan_valid runtimeBytecode 87 140 (by decide +kernel)), jumpdest]
    have first := runtime_run split with [dup1, push4 ⟨0x5c1bba38⟩, eq, push2 ⟨136⟩,
      jumpiNT (by decide +kernel)]
    have second := runtime_run first with [dup1, push4 ⟨0x88af9950⟩, eq, push2 ⟨195⟩,
      jumpiNT (by decide +kernel)]
    have third := runtime_run second with [dup1, push4 ⟨0x9588eca2⟩, eq, push2 ⟨228⟩,
      jumpiNT (by decide +kernel)]
    exact ⟨_, _, runtime_run third with [dup1, push4 ⟨0xba873065⟩, eq, push2 ⟨263⟩,
      jumpiT (by decide +kernel) (jumpScan_valid runtimeBytecode 263 350 (by decide +kernel))]⟩
  | backing =>
    have split := runtime_run loaded with [dup1, push4 ⟨0xbb3ef682⟩, gt, push2 ⟨87⟩,
      jumpiNT (by decide +kernel)]
    have first := runtime_run split with [dup1, push4 ⟨0xbb3ef682⟩, eq, push2 ⟨284⟩,
      jumpiNT (by decide +kernel)]
    exact ⟨_, _, runtime_run first with [dup1, push4 ⟨0xc9503fe2⟩, eq, push2 ⟨315⟩,
      jumpiT (by decide +kernel) (jumpScan_valid runtimeBytecode 315 350 (by decide +kernel))]⟩

/-- Accepted scalar getter calls return the exact word and preserve the account map. -/
theorem scalar_getter_xi_success {cA gh bl σ σ₀ A I} {g : Sat256}
    {cA' σ' gas substate output} (getter : ScalarGetter) (code : I.code = runtimeBytecode)
    (length : 4 ≤ I.calldata.size) (bounded : I.calldata.size < UInt256.size)
    (selector : solcSelectorWord I = scalarSelector getter)
    (success : Ξ cA gh bl σ σ₀ g.toUInt256 A I = .ok (.success (cA', σ', gas, substate) output)) :
    I.weiValue = ⟨0⟩ ∧ cA' = cA ∧ σ' = σ ∧
      output = UInt256.toByteArray (solcSlotWord σ I (scalarSlot getter)) := by
  obtain ⟨_, _, reached⟩ := scalar_getter_dispatch (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) getter code length bounded selector
  by_cases value : I.weiValue = ⟨0⟩
  · have returned := scalar_getter_return getter [scalarSelector getter] (by simp) value reached
    rcases returned.xiResult code with failed | ⟨gas', substate', actual⟩
    · rw [success] at failed
      cases failed
    · rw [success] at actual
      cases actual
      exact ⟨value, rfl, rfl, rfl⟩
  · have rejected := scalar_getter_nonpayable getter [scalarSelector getter] (by simp) value reached
    rcases rejected.xiResult code with failed | ⟨gas', data, actual⟩
    · rw [success] at failed
      cases failed
    · rw [success] at actual
      cases actual

end Rollup.EVM
