import proofs.RuntimeBytecode

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Rollup.EVM

/-- The shared return tail returns one word without changing accounts. -/
theorem runtime_return_tail {I : ExecutionEnv} {g : Sat256} {s0 : Ethereum.State}
    {mem rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (word : UInt256) (rest : List UInt256) (space : rest.length + 3 ≤ 1024)
    (pointer : (if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨
        (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩ else
        UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) = ⟨128⟩)
    (output : mem.readWithPadding 128 32 = UInt256.toByteArray word)
    (reached : RD runtimeBytecode I g s0 ⟨186⟩ (⟨160⟩ :: rest) mem (UInt256.ofNat 5)
      rdata acc k C) : RDret runtimeBytecode g s0 acc (UInt256.toByteArray word) := by
  have beforeLoad := runtime_run reached with [jumpdest, push1 ⟨64⟩]
  have loaded := beforeLoad.mload 0 ⟨128⟩ (UInt256.ofNat 5)
    (by decide +kernel) mem_cost pointer (by decide) (by evm_ov)
  have returned := runtime_run loaded with [dup1, swap2, sub, swap1]
  exact returned.ret 0 (UInt256.toByteArray word) (by decide +kernel) mem_cost
    (by convert output using 1) (by evm_ov)

/-- The word encoder writes its result at the free memory pointer. -/
theorem runtime_return_word {I : ExecutionEnv} {g : Sat256} {s0 : Ethereum.State}
    {mem memout rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (word : UInt256) (rest : List UInt256) (space : rest.length + 3 ≤ 1024)
    (pointer : (if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨
        (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩ else
        UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) = ⟨128⟩)
    (stored : (UInt256.toByteArray word).write 0 mem 128 32 = memout)
    (pointerAfter : (if (⟨64⟩ : UInt256).toNat ≥ memout.size ∨
        (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩ else
        UInt256.ofNat (fromByteArrayBigEndian (memout.readWithPadding (⟨64⟩ : UInt256).toNat 32))) = ⟨128⟩)
    (output : memout.readWithPadding 128 32 = UInt256.toByteArray word)
    (reached : RD runtimeBytecode I g s0 ⟨249⟩ (word :: rest) mem (UInt256.ofNat 3)
      rdata acc k C) : RDret runtimeBytecode g s0 acc (UInt256.toByteArray word) := by
  have beforeLoad := runtime_run reached with [jumpdest, push1 ⟨64⟩]
  have loaded := beforeLoad.mload 0 ⟨128⟩ (UInt256.ofNat 3)
    (by decide +kernel) mem_cost pointer (by decide) (by evm_ov)
  have beforeStore := runtime_run loaded with [swap1, dup2]
  have saved := beforeStore.mstore 6 memout (UInt256.ofNat 5)
    (by decide +kernel) mem_cost stored (by decide) (by evm_ov)
  have tail := runtime_run saved with [push1 ⟨32⟩, add, push2 ⟨186⟩,
    jump (jumpScan_valid runtimeBytecode 186 200 (by decide +kernel))]
  exact runtime_return_tail word rest space pointerAfter output (by exact tail)

end Rollup.EVM
