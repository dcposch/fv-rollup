import proofs.StaticStore
import proofs.RuntimeMutationLocks
import proofs.DepositBytecodeGuards

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2048
set_option maxHeartbeats 2000000

namespace Rollup.EVM

/-- A static batch cannot pass its lock guard. -/
theorem batch_static_guard {I : ExecutionEnv} {g : Sat256} {start : Ethereum.State}
    {mem data : ByteArray} {words : UInt256} {cA : Batteries.RBSet AccountAddress compare}
    {accounts : AccountMap} {k cost : Nat}
    (stack : List UInt256) (space : stack.length + 2 ≤ 1024)
    (readonly : I.perm = false)
    (reached : RD runtimeBytecode I g start ⟨441⟩ stack mem words data (cA, accounts) k cost)
    (after : Ethereum.State) (output : ByteArray) :
    X (g.toNat + 1) (D_J runtimeBytecode 0) start ≠ .ok (.success after output) := by
  by_cases unlocked : solcSlotWord accounts I ⟨6⟩ = ⟨0⟩
  · have slot := runtime_run reached with [jumpdest, push1 ⟨6⟩]
    obtain ⟨_, _, loaded⟩ := slot.sload (by decide +kernel) (by evm_ov)
    dsimp only [solcSlotWord] at unlocked
    rw [unlocked] at loaded
    have store := runtime_run loaded with [iszero, push2 ⟨453⟩,
      jumpiT (by decide) (jumpScan_valid runtimeBytecode 453 480 (by decide +kernel)),
      jumpdest, push1 ⟨1⟩, push1 ⟨6⟩]
    exact rd_sstore_static_no_success store readonly (by decide +kernel) after output
  · exact rd_revert_no_success (batch_bytecode_locked stack space unlocked reached) after output

/-- A static withdrawal cannot pass its lock guard. -/
theorem withdrawal_static_guard {I : ExecutionEnv} {g : Sat256} {start : Ethereum.State}
    {mem data : ByteArray} {words : UInt256} {cA : Batteries.RBSet AccountAddress compare}
    {accounts : AccountMap} {k cost : Nat}
    (stack : List UInt256) (space : stack.length + 2 ≤ 1024)
    (readonly : I.perm = false)
    (reached : RD runtimeBytecode I g start ⟨843⟩ stack mem words data (cA, accounts) k cost)
    (after : Ethereum.State) (output : ByteArray) :
    X (g.toNat + 1) (D_J runtimeBytecode 0) start ≠ .ok (.success after output) := by
  by_cases unlocked : solcSlotWord accounts I ⟨6⟩ = ⟨0⟩
  · have slot := runtime_run reached with [jumpdest, push1 ⟨6⟩]
    obtain ⟨_, _, loaded⟩ := slot.sload (by decide +kernel) (by evm_ov)
    dsimp only [solcSlotWord] at unlocked
    rw [unlocked] at loaded
    have store := runtime_run loaded with [iszero, push2 ⟨855⟩,
      jumpiT (by decide) (jumpScan_valid runtimeBytecode 855 880 (by decide +kernel)),
      jumpdest, push1 ⟨1⟩, push1 ⟨6⟩]
    exact rd_sstore_static_no_success store readonly (by decide +kernel) after output
  · exact rd_revert_no_success (withdrawal_bytecode_locked stack space unlocked reached) after output

/-- A static deposit cannot pass its lock guard. -/
theorem deposit_static_guard {I : ExecutionEnv} {g : Sat256} {start : Ethereum.State}
    {mem data : ByteArray} {words : UInt256} {cA : Batteries.RBSet AccountAddress compare}
    {accounts : AccountMap} {k cost : Nat}
    (stack : List UInt256) (space : stack.length + 2 ≤ 1024)
    (readonly : I.perm = false)
    (reached : RD runtimeBytecode I g start ⟨1045⟩ stack mem words data (cA, accounts) k cost)
    (after : Ethereum.State) (output : ByteArray) :
    X (g.toNat + 1) (D_J runtimeBytecode 0) start ≠ .ok (.success after output) := by
  by_cases unlocked : solcSlotWord accounts I ⟨6⟩ = ⟨0⟩
  · have slot := runtime_run reached with [jumpdest, push1 ⟨6⟩]
    obtain ⟨_, _, loaded⟩ := slot.sload (by decide +kernel) (by evm_ov)
    dsimp only [solcSlotWord] at unlocked
    rw [unlocked] at loaded
    have store := runtime_run loaded with [iszero, push2 ⟨1057⟩,
      jumpiT (by decide) (jumpScan_valid runtimeBytecode 1057 1080 (by decide +kernel)),
      jumpdest, push1 ⟨1⟩, push1 ⟨6⟩]
    exact rd_sstore_static_no_success store readonly (by decide +kernel) after output
  · exact rd_revert_no_success (deposit_bytecode_locked stack space unlocked reached) after output

end Rollup.EVM
