import proofs.RuntimeBytecode

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Rollup.EVM

/-- The address check returns only for a canonical 160-bit word. -/
theorem runtime_address_check {I : ExecutionEnv} {g : Sat256} {s0 : Ethereum.State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (word ret : UInt256) (rest : List UInt256)
    (canonical : word.toNat < _root_.EVM.addressModulus)
    (destination : (D_J runtimeBytecode 0).contains ret = true)
    (space : rest.length + 6 ≤ 1024)
    (reached : RD runtimeBytecode I g s0 ⟨1165⟩ (word :: ret :: rest) mem aw rdata acc k C) :
    ∃ k' C', RD runtimeBytecode I g s0 ret rest mem aw rdata acc k' C' := by
  have mask : UInt256.sub (UInt256.shiftLeft ⟨1⟩ ⟨160⟩) ⟨1⟩ = solcAddrMask := by decide
  have guard := runtime_run reached with [jumpdest, push1 ⟨1⟩, push1 ⟨1⟩,
    push1 ⟨160⟩, shl, sub, dup2, and, dup2, eq, push2 ⟨1185⟩]
  rw [mask, solcAddrCanon_eq canonical] at guard
  exact ⟨_, _, runtime_run guard with [
    jumpiT (by decide) (jumpScan_valid runtimeBytecode 1185 1200 (by decide +kernel)),
    jumpdest, pop, jump destination]⟩

/-- A word with nonzero high address bits fails the address check. -/
theorem runtime_address_check_reject {I : ExecutionEnv} {g : Sat256} {s0 : Ethereum.State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (word ret : UInt256) (rest : List UInt256)
    (noncanonical : ¬ word.toNat < _root_.EVM.addressModulus)
    (space : rest.length + 6 ≤ 1024)
    (reached : RD runtimeBytecode I g s0 ⟨1165⟩ (word :: ret :: rest) mem aw rdata acc k C) :
    RDrev runtimeBytecode g s0 := by
  have mask : UInt256.sub (UInt256.shiftLeft ⟨1⟩ ⟨160⟩) ⟨1⟩ = solcAddrMask := by decide
  have different : word ≠ UInt256.land word solcAddrMask := by
    intro same
    have smaller := solcAddrMask_result_canonical word
    rw [← same] at smaller
    exact noncanonical smaller
  have guard := runtime_run reached with [jumpdest, push1 ⟨1⟩, push1 ⟨1⟩,
    push1 ⟨160⟩, shl, sub, dup2, and, dup2, eq, push2 ⟨1185⟩]
  rw [mask, u256_eq_of_ne different] at guard
  have rejected := runtime_run guard with [jumpiNT rfl, push0, dup1]
  exact rejected.rev 0 (by decide +kernel)
    (fun s _ stack => memExpRevert0 s stack) (by evm_ov)

/-- Decode one address argument and return to the caller. -/
theorem runtime_address_decode {I : ExecutionEnv} {g : Sat256} {s0 : Ethereum.State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (ret : UInt256) (rest : List UInt256)
    (length : 36 ≤ I.calldata.size) (signedBound : I.calldata.size < 2 ^ 255 + 4)
    (bounded : I.calldata.size < UInt256.size)
    (canonical : (calldataWord I.calldata 4).toNat < _root_.EVM.addressModulus)
    (destination : (D_J runtimeBytecode 0).contains ret = true)
    (space : rest.length + 11 ≤ 1024)
    (reached : RD runtimeBytecode I g s0 ⟨1331⟩
      (⟨4⟩ :: UInt256.ofNat I.calldata.size :: ret :: rest) mem aw rdata acc k C) :
    ∃ k' C', RD runtimeBytecode I g s0 ret (calldataWord I.calldata 4 :: rest)
      mem aw rdata acc k' C' := by
  have sizeCheck := solcDecodeLenCheckOk_4_32 length signedBound bounded
  have guard := runtime_run reached with [jumpdest, push0, push1 ⟨32⟩,
    dup3, dup5, sub, slt, iszero, push2 ⟨1347⟩]
  have entered := runtime_run guard with [
    jumpiT (by rw [sizeCheck]; decide)
      (jumpScan_valid runtimeBytecode 1347 1360 (by decide +kernel)),
    jumpdest, dup2, calldataload, push2 ⟨1358⟩, dup2, push2 ⟨1165⟩,
    jump (jumpScan_valid runtimeBytecode 1165 1180 (by decide +kernel))]
  obtain ⟨_, _, checked⟩ := runtime_address_check (calldataWord I.calldata 4) ⟨1358⟩
    (calldataWord I.calldata 4 :: ⟨0⟩ :: ⟨4⟩ :: UInt256.ofNat I.calldata.size :: ret :: rest)
    canonical (jumpScan_valid runtimeBytecode 1358 1370 (by decide +kernel))
    (by simp only [List.length_cons]; omega) entered
  exact ⟨_, _, runtime_run checked with [jumpdest, swap4, swap3, pop, pop, pop, jump destination]⟩

end Rollup.EVM
