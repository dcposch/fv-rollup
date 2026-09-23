import proofs.RuntimeReturn

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Rollup.EVM

/-- The sequencer selector reaches its getter without changing accounts. -/
theorem sequencer_getter_dispatch {cA gh bl σ σ₀ A I} {g : Sat256}
    (code : I.code = runtimeBytecode) (length : 4 ≤ I.calldata.size)
    (bounded : I.calldata.size < UInt256.size)
    (selector : solcSelectorWord I = ⟨0x5c1bba38⟩) :
    ∃ k C, RD runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨136⟩
      [⟨0x5c1bba38⟩] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, loaded⟩ := runtime_selector (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) code length bounded
  rw [selector] at loaded
  have split := runtime_run loaded with [dup1, push4 ⟨0xbb3ef682⟩, gt, push2 ⟨87⟩,
    jumpiT (by decide +kernel) (jumpScan_valid runtimeBytecode 87 140 (by decide +kernel)), jumpdest]
  exact ⟨_, _, runtime_run split with [dup1, push4 ⟨0x5c1bba38⟩, eq, push2 ⟨136⟩,
    jumpiT (by decide +kernel) (jumpScan_valid runtimeBytecode 136 150 (by decide +kernel))]⟩

/-- The sequencer getter rejects call value. -/
theorem sequencer_getter_nonpayable {I : ExecutionEnv} {g : Sat256} {s0 : Ethereum.State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (rest : List UInt256) (space : rest.length + 3 ≤ 1024)
    (value : I.weiValue ≠ ⟨0⟩)
    (reached : RD runtimeBytecode I g s0 ⟨136⟩ rest mem aw rdata acc k C) :
    RDrev runtimeBytecode g s0 := by
  have guarded := runtime_run reached with [jumpdest, callvalue, dup1, iszero, push2 ⟨147⟩]
  have rejected := runtime_run guarded with [jumpiNT (isZero_eq_zero_of_ne value), push0, dup1]
  exact rejected.rev 0 (by decide +kernel)
    (fun s _ stack => memExpRevert0 s stack) (by evm_ov)

/-- The sequencer getter masks the packed word and preserves accounts. -/
theorem sequencer_getter_return {I : ExecutionEnv} {g : Sat256} {s0 : Ethereum.State}
    {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : Nat}
    (rest : List UInt256) (space : rest.length + 6 ≤ 1024)
    (value : I.weiValue = ⟨0⟩)
    (reached : RD runtimeBytecode I g s0 ⟨136⟩ rest solcFreePtrMem
      (UInt256.ofNat 3) rdata (cA, σ) k C) :
    RDret runtimeBytecode g s0 (cA, σ)
      (UInt256.toByteArray (UInt256.land (solcSlotWord σ I ⟨0⟩) solcAddrMask)) := by
  have mask : UInt256.sub (UInt256.shiftLeft ⟨1⟩ ⟨160⟩) ⟨1⟩ = solcAddrMask := by decide
  have guarded := runtime_run reached with [jumpdest, callvalue, dup1, iszero, push2 ⟨147⟩]
  have accepted := runtime_run guarded with [jumpiT (by rw [value]; decide)
    (jumpScan_valid runtimeBytecode 147 170 (by decide +kernel)), jumpdest, pop, push0]
  obtain ⟨_, _, loaded⟩ := accepted.sload (by decide +kernel) (by evm_ov)
  have cleaned := runtime_run loaded with [push2 ⟨166⟩, swap1, push1 ⟨1⟩, push1 ⟨1⟩,
    push1 ⟨160⟩, shl, sub, and, dup2,
    jump (jumpScan_valid runtimeBytecode 166 190 (by decide +kernel)), jumpdest, push1 ⟨64⟩]
  rw [mask, u256_land_comm solcAddrMask] at cleaned
  have pointer := cleaned.mload 0 ⟨128⟩ (UInt256.ofNat 3)
    (by decide +kernel) mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov)
  have beforeStore := runtime_run pointer with [push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩,
    shl, sub, swap1, swap2, and, dup2]
  rw [mask, solcAddrMask_clean (solcAddrMask_result_canonical _)] at beforeStore
  have saved := beforeStore.mstore 6
    (solcReturnMem (UInt256.land (solcSlotWord σ I ⟨0⟩) solcAddrMask)) (UInt256.ofNat 5)
    (by decide +kernel) mem_cost rfl (by decide) (by evm_ov)
  have tail := runtime_run saved with [push1 ⟨32⟩, add]
  exact runtime_return_tail _ (⟨166⟩ :: rest) (by evm_ov)
    (solcReturnMem_mload64 _) (solcReturnMem_read128 _) tail

/-- Accepted sequencer calls return its address and preserve the account map. -/
theorem sequencer_getter_xi_success {cA gh bl σ σ₀ A I} {g : Sat256}
    {cA' σ' gas substate output} (code : I.code = runtimeBytecode)
    (length : 4 ≤ I.calldata.size) (bounded : I.calldata.size < UInt256.size)
    (selector : solcSelectorWord I = ⟨0x5c1bba38⟩)
    (success : Ξ cA gh bl σ σ₀ g.toUInt256 A I = .ok (.success (cA', σ', gas, substate) output)) :
    I.weiValue = ⟨0⟩ ∧ cA' = cA ∧ σ' = σ ∧
      output = UInt256.toByteArray (UInt256.land (solcSlotWord σ I ⟨0⟩) solcAddrMask) := by
  obtain ⟨_, _, reached⟩ := sequencer_getter_dispatch (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) code length bounded selector
  by_cases value : I.weiValue = ⟨0⟩
  · have returned := sequencer_getter_return [⟨0x5c1bba38⟩] (by decide) value reached
    rcases returned.xiResult code with failed | ⟨gas', substate', actual⟩
    · rw [success] at failed
      cases failed
    · rw [success] at actual
      cases actual
      exact ⟨value, rfl, rfl, rfl⟩
  · have rejected := sequencer_getter_nonpayable [⟨0x5c1bba38⟩] (by decide) value reached
    rcases rejected.xiResult code with failed | ⟨gas', data, actual⟩
    · rw [success] at failed
      cases failed
    · rw [success] at actual
      cases actual

end Rollup.EVM
