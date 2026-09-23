import proofs.RuntimeDecode
import proofs.RuntimeSwap

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Rollup.EVM

def batchFirstRest (I : ExecutionEnv) (ret : UInt256) (rest : List UInt256) : List UInt256 :=
  calldataWord I.calldata 100 :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
  calldataWord I.calldata 68 :: calldataWord I.calldata 36 :: calldataWord I.calldata 4 ::
  ⟨4⟩ :: UInt256.ofNat I.calldata.size :: ret :: rest

def batchSecondRest (I : ExecutionEnv) (ret : UInt256) (rest : List UInt256) : List UInt256 :=
  calldataWord I.calldata 164 :: ⟨0⟩ :: ⟨0⟩ :: calldataWord I.calldata 132 ::
  calldataWord I.calldata 100 :: calldataWord I.calldata 68 :: calldataWord I.calldata 36 ::
  calldataWord I.calldata 4 :: ⟨4⟩ :: UInt256.ofNat I.calldata.size :: ret :: rest

def batchDecodedStack (I : ExecutionEnv) (rest : List UInt256) : List UInt256 :=
  calldataWord I.calldata 196 :: calldataWord I.calldata 164 :: calldataWord I.calldata 132 ::
  calldataWord I.calldata 100 :: calldataWord I.calldata 68 :: calldataWord I.calldata 36 ::
  calldataWord I.calldata 4 :: rest

/-- The batch decoder checks length and loads the first address. -/
theorem batch_decode_first {I : ExecutionEnv} {g : Sat256} {s0 : Ethereum.State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (ret : UInt256) (rest : List UInt256)
    (length : 228 ≤ I.calldata.size) (signedBound : I.calldata.size < 2 ^ 255 + 4)
    (bounded : I.calldata.size < UInt256.size) (space : rest.length + 14 ≤ 1024)
    (reached : RD runtimeBytecode I g s0 ⟨1188⟩
      (⟨4⟩ :: UInt256.ofNat I.calldata.size :: ret :: rest) mem aw rdata acc k C) :
    ∃ k' C', RD runtimeBytecode I g s0 ⟨1165⟩
      (calldataWord I.calldata 100 :: ⟨1242⟩ :: batchFirstRest I ret rest)
      mem aw rdata acc k' C' := by
  have sizeCheck : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨224⟩ = ⟨0⟩ :=
    solcCalldataStaticLenCheckOk (words := 7) length signedBound bounded
  have guard := runtime_run reached with [jumpdest, push0, dup1, push0, dup1, push0, dup1,
    push0, push1 ⟨224⟩, dup9, dup11, sub, slt, iszero, push2 ⟨1210⟩]
  have entered := runtime_run guard with [jumpiT (by rw [sizeCheck]; decide)
    (jumpScan_valid runtimeBytecode 1210 1260 (by decide +kernel)), jumpdest,
    dup8, calldataload, swap7, pop, push1 ⟨32⟩, dup9, add, calldataload, swap6, pop,
    push1 ⟨64⟩, dup9, add, calldataload, swap5, pop,
    push1 ⟨96⟩, dup9, add, calldataload, push2 ⟨1242⟩, dup2, push2 ⟨1165⟩,
    jump (jumpScan_valid runtimeBytecode 1165 1180 (by decide +kernel))]
  exact ⟨_, _, entered⟩

/-- The batch decoder loads the second address after the first address check. -/
theorem batch_decode_second {I : ExecutionEnv} {g : Sat256} {s0 : Ethereum.State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (ret : UInt256) (rest : List UInt256) (space : rest.length + 14 ≤ 1024)
    (reached : RD runtimeBytecode I g s0 ⟨1242⟩ (batchFirstRest I ret rest)
      mem aw rdata acc k C) :
    ∃ k' C', RD runtimeBytecode I g s0 ⟨1165⟩
      (calldataWord I.calldata 164 :: ⟨1265⟩ :: batchSecondRest I ret rest)
      mem aw rdata acc k' C' := by
  dsimp only [batchFirstRest] at reached
  exact ⟨_, _, runtime_run reached with [jumpdest, swap4, pop,
    push1 ⟨128⟩, dup9, add, calldataload, swap3, pop,
    push1 ⟨160⟩, dup9, add, calldataload, push2 ⟨1265⟩, dup2, push2 ⟨1165⟩,
    jump (jumpScan_valid runtimeBytecode 1165 1180 (by decide +kernel))]⟩

/-- The batch decoder returns all seven words in compiler stack order. -/
theorem batch_decode_tail {I : ExecutionEnv} {g : Sat256} {s0 : Ethereum.State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (ret : UInt256) (rest : List UInt256) (space : rest.length + 11 ≤ 1024)
    (destination : (D_J runtimeBytecode 0).contains ret = true)
    (reached : RD runtimeBytecode I g s0 ⟨1265⟩ (batchSecondRest I ret rest)
      mem aw rdata acc k C) :
    ∃ k' C', RD runtimeBytecode I g s0 ret (batchDecodedStack I rest)
      mem aw rdata acc k' C' := by
  dsimp only [batchSecondRest] at reached
  exact ⟨_, _, runtime_run reached with [jumpdest, swap7, swap10, swap6, swap9, pop,
    swap4, swap7, swap3, swap6, swap2, swap5, swap2, swap4, pop, pop,
    push1 ⟨192⟩, swap1, swap2, add, calldataload, swap1, jump destination]⟩

/-- Reject a batch whose signed length check fails. -/
theorem batch_decode_bad_length {I : ExecutionEnv} {g : Sat256} {s0 : Ethereum.State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (ret : UInt256) (rest : List UInt256) (space : rest.length + 13 ≤ 1024)
    (badLength : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨224⟩ = ⟨1⟩)
    (reached : RD runtimeBytecode I g s0 ⟨1188⟩
      (⟨4⟩ :: UInt256.ofNat I.calldata.size :: ret :: rest) mem aw rdata acc k C) :
    RDrev runtimeBytecode g s0 := by
  have guard := runtime_run reached with [jumpdest, push0, dup1, push0, dup1, push0, dup1,
    push0, push1 ⟨224⟩, dup9, dup11, sub, slt, iszero, push2 ⟨1210⟩]
  rw [badLength] at guard
  have rejected := runtime_run guard with [jumpiNT (by decide), push0, dup1]
  exact rejected.rev 0 (by decide +kernel)
    (fun s _ stack => memExpRevert0 s stack) (by evm_ov)

end Rollup.EVM
