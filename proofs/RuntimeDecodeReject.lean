import proofs.RuntimeDecode

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Rollup.EVM

/-- Reject when the one-word decoder's signed length check fails. -/
theorem runtime_address_bad_length {I : ExecutionEnv} {g : Sat256} {s0 : Ethereum.State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (ret : UInt256) (rest : List UInt256) (space : rest.length + 7 ≤ 1024)
    (badLength : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩)
    (reached : RD runtimeBytecode I g s0 ⟨1331⟩
      (⟨4⟩ :: UInt256.ofNat I.calldata.size :: ret :: rest) mem aw rdata acc k C) :
    RDrev runtimeBytecode g s0 := by
  have guard := runtime_run reached with [jumpdest, push0, push1 ⟨32⟩,
    dup3, dup5, sub, slt, iszero, push2 ⟨1347⟩]
  rw [badLength] at guard
  have rejected := runtime_run guard with [jumpiNT (by decide), push0, dup1]
  exact rejected.rev 0 (by decide +kernel)
    (fun s _ stack => memExpRevert0 s stack) (by evm_ov)

/-- Reject a noncanonical address after the length check. -/
theorem runtime_address_bad_word {I : ExecutionEnv} {g : Sat256} {s0 : Ethereum.State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (ret : UInt256) (rest : List UInt256)
    (length : 36 ≤ I.calldata.size) (signedBound : I.calldata.size < 2 ^ 255 + 4)
    (bounded : I.calldata.size < UInt256.size)
    (noncanonical : ¬ (calldataWord I.calldata 4).toNat < _root_.EVM.addressModulus)
    (space : rest.length + 11 ≤ 1024)
    (reached : RD runtimeBytecode I g s0 ⟨1331⟩
      (⟨4⟩ :: UInt256.ofNat I.calldata.size :: ret :: rest) mem aw rdata acc k C) :
    RDrev runtimeBytecode g s0 := by
  have sizeCheck := solcDecodeLenCheckOk_4_32 length signedBound bounded
  have guard := runtime_run reached with [jumpdest, push0, push1 ⟨32⟩,
    dup3, dup5, sub, slt, iszero, push2 ⟨1347⟩]
  have entered := runtime_run guard with [
    jumpiT (by rw [sizeCheck]; decide)
      (jumpScan_valid runtimeBytecode 1347 1360 (by decide +kernel)),
    jumpdest, dup2, calldataload, push2 ⟨1358⟩, dup2, push2 ⟨1165⟩,
    jump (jumpScan_valid runtimeBytecode 1165 1180 (by decide +kernel))]
  exact runtime_address_check_reject (calldataWord I.calldata 4) ⟨1358⟩
    (calldataWord I.calldata 4 :: ⟨0⟩ :: ⟨4⟩ :: UInt256.ofNat I.calldata.size :: ret :: rest)
    noncanonical (by simp only [List.length_cons]; omega) entered

end Rollup.EVM
