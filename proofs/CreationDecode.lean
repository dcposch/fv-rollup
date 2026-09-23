import proofs.CreationMemory

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Rollup.EVM

/-- Load the two constructor words and check the address encoding. -/
theorem creation_load_args {I : ExecutionEnv} {g : Sat256} {s0 : Ethereum.State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (sequencer root : UInt256)
    (canonical : sequencer.toNat < _root_.EVM.addressModulus)
    (reached : RD (creationBytecode ++ creationArgs sequencer root) I g s0 ⟨16⟩ []
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty acc k C) :
    ∃ k' C', RD (creationBytecode ++ creationArgs sequencer root) I g s0 ⟨43⟩
      [root, sequencer] (creationArgMem sequencer root) (UInt256.ofNat 6)
      ByteArray.empty acc k' C' := by
  have beforeSize := creation_run reached with [push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by creation_decode_step)
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov),
    push2 ⟨1594⟩, codesize]
  rw [ByteArray.size_append, creation_size, creationArgs_size] at beforeSize
  have beforeCopy := creation_run beforeSize with [sub, dup1, push2 ⟨1594⟩, dup4]
  have copied := beforeCopy.codecopy 9 (creationCopiedMem sequencer root) (UInt256.ofNat 6)
    (by creation_decode_step) mem_cost (creation_codecopy sequencer root) (by decide) (by evm_ov)
  have beforePointer := creation_run copied with [dup2, add, push1 ⟨64⟩, dup2, swap1]
  have pointer := beforePointer.mstore 0 (creationArgMem sequencer root) (UInt256.ofNat 6)
    (by creation_decode_step) mem_cost rfl (by decide) (by evm_ov)
  have decoding := creation_run pointer with [push1 ⟨43⟩, swap2, push1 ⟨99⟩,
    jump (D_J_contains_append_left _ _ _ (jumpScan_valid creationBytecode 99 100 (by decide))),
    jumpdest, push0, dup1, push1 ⟨64⟩, dup4, dup6, sub, slt, iszero, push1 ⟨115⟩,
    jumpiT (by decide)
      (D_J_contains_append_left _ _ _ (jumpScan_valid creationBytecode 115 110 (by decide))),
    jumpdest, dup3]
  have loadedSeq := decoding.mload 0 sequencer (UInt256.ofNat 6)
    (by creation_decode_step) mem_cost
    (mloadWordValue_of_readWithPadding (by rw [creationArgMem_size]; decide) (by decide)
      (creationArgMem_read128 sequencer root)) (by decide) (by evm_ov)
  have addressCheck := creation_run loadedSeq with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup2, and, dup2, eq, push1 ⟨136⟩]
  have mask : UInt256.sub (UInt256.shiftLeft ⟨1⟩ ⟨160⟩) ⟨1⟩ = solcAddrMask := by decide
  have clean := solcAddrMask_clean canonical
  have beforeRoot := creation_run addressCheck with [
    jumpiT (by rw [mask, clean, uInt256_eq_self]; decide)
      (D_J_contains_append_left _ _ _ (jumpScan_valid creationBytecode 136 140 (by decide))),
    jumpdest, push1 ⟨32⟩, swap4, swap1, swap4, add]
  have loadedRoot := beforeRoot.mload 0 root (UInt256.ofNat 6)
    (by creation_decode_step) mem_cost
    (mloadWordValue_of_readWithPadding (by rw [creationArgMem_size]; decide) (by decide)
      (creationArgMem_read160 sequencer root)) (by decide) (by evm_ov)
  exact ⟨_, _, creation_run loadedRoot with [swap3, swap5, swap3, swap4, pop, pop, pop,
    jump (D_J_contains_append_left _ _ _ (jumpScan_valid creationBytecode 43 50 (by decide)))]⟩

end Rollup.EVM
