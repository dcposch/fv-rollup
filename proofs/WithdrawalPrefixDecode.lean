import proofs.RuntimePrefixAddress

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Rollup.EVM

/-- Decode the withdrawal owner and amount without changing accounts. -/
theorem withdrawal_prefix_decode {I : ExecutionEnv} {target child : Ethereum.State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (ret : UInt256) (rest : List UInt256)
    (length : 68 ≤ I.calldata.size) (signedBound : I.calldata.size < 2 ^ 255 + 4)
    (bounded : I.calldata.size < UInt256.size)
    (canonical : (calldataWord I.calldata 4).toNat < _root_.EVM.addressModulus)
    (destination : (D_J runtimeBytecode 0).contains ret = true)
    (space : rest.length + 12 ≤ 1024)
    (reached : PCR runtimeBytecode I target child ⟨1289⟩
      (⟨4⟩ :: UInt256.ofNat I.calldata.size :: ret :: rest) mem aw rdata acc) :
    PCR runtimeBytecode I target child ret
      (calldataWord I.calldata 36 :: calldataWord I.calldata 4 :: rest)
      mem aw rdata acc := by
  have sizeCheck := solcDecodeLenCheckOk_4_64 length signedBound bounded
  have guard := runtime_run reached with [jumpdest, push0, dup1, push1 ⟨64⟩,
    dup4, dup6, sub, slt, iszero, push2 ⟨1306⟩]
  have entered := runtime_run guard with [
    jumpiT (by rw [sizeCheck]; decide)
      (jumpScan_valid runtimeBytecode 1306 1331 (by decide +kernel)),
    jumpdest, dup3, calldataload, push2 ⟨1317⟩, dup2, push2 ⟨1165⟩,
    jump (jumpScan_valid runtimeBytecode 1165 1180 (by decide +kernel))]
  have checked := runtime_prefix_address_check (calldataWord I.calldata 4) ⟨1317⟩
    (calldataWord I.calldata 4 :: ⟨0⟩ :: ⟨0⟩ :: ⟨4⟩ :: UInt256.ofNat I.calldata.size :: ret :: rest)
    canonical (jumpScan_valid runtimeBytecode 1317 1340 (by decide +kernel)) (by evm_ov) entered
  exact runtime_run checked with [jumpdest, swap5, push1 ⟨32⟩, swap4, swap1,
    swap4, add, calldataload, swap4, pop, pop, pop, jump destination]

/-- Reject a withdrawal whose signed length check fails. -/
theorem withdrawal_prefix_decode_bad_length {I : ExecutionEnv} {target child : Ethereum.State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (ret : UInt256) (rest : List UInt256) (space : rest.length + 8 ≤ 1024)
    (badLength : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨1⟩)
    (reached : PCR runtimeBytecode I target child ⟨1289⟩
      (⟨4⟩ :: UInt256.ofNat I.calldata.size :: ret :: rest) mem aw rdata acc) :
    False := by
  have guard := runtime_run reached with [jumpdest, push0, dup1, push1 ⟨64⟩,
    dup4, dup6, sub, slt, iszero, push2 ⟨1306⟩]
  rw [badLength] at guard
  have rejected := runtime_run guard with [jumpiNT (by decide), push0, dup1]
  exact rejected.halt (arg := none) (by decide +kernel) (Or.inr (Or.inr (Or.inl rfl)))

/-- Reject a withdrawal whose address has nonzero high bits. -/
theorem withdrawal_prefix_decode_bad_owner {I : ExecutionEnv} {target child : Ethereum.State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (ret : UInt256) (rest : List UInt256)
    (length : 68 ≤ I.calldata.size) (signedBound : I.calldata.size < 2 ^ 255 + 4)
    (bounded : I.calldata.size < UInt256.size)
    (noncanonical : ¬ (calldataWord I.calldata 4).toNat < _root_.EVM.addressModulus)
    (space : rest.length + 12 ≤ 1024)
    (reached : PCR runtimeBytecode I target child ⟨1289⟩
      (⟨4⟩ :: UInt256.ofNat I.calldata.size :: ret :: rest) mem aw rdata acc) :
    False := by
  have sizeCheck := solcDecodeLenCheckOk_4_64 length signedBound bounded
  have guard := runtime_run reached with [jumpdest, push0, dup1, push1 ⟨64⟩,
    dup4, dup6, sub, slt, iszero, push2 ⟨1306⟩]
  have entered := runtime_run guard with [
    jumpiT (by rw [sizeCheck]; decide)
      (jumpScan_valid runtimeBytecode 1306 1331 (by decide +kernel)),
    jumpdest, dup3, calldataload, push2 ⟨1317⟩, dup2, push2 ⟨1165⟩,
    jump (jumpScan_valid runtimeBytecode 1165 1180 (by decide +kernel))]
  exact runtime_prefix_address_check_reject (calldataWord I.calldata 4) ⟨1317⟩
    (calldataWord I.calldata 4 :: ⟨0⟩ :: ⟨0⟩ :: ⟨4⟩ :: UInt256.ofNat I.calldata.size :: ret :: rest)
    noncanonical (by evm_ov) entered

end Rollup.EVM
