import proofs.RuntimeDecodeReject

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Rollup.EVM

/-- Classify decoding from the actual word-sized guard, without a calldata-size premise. -/
theorem runtime_address_decode_any {I : ExecutionEnv} {g : Sat256} {s0 : Ethereum.State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (ret : UInt256) (rest : List UInt256)
    (destination : (D_J runtimeBytecode 0).contains ret = true)
    (space : rest.length + 11 ≤ 1024)
    (reached : RD runtimeBytecode I g s0 ⟨1331⟩
      (⟨4⟩ :: UInt256.ofNat I.calldata.size :: ret :: rest) mem aw rdata acc k C) :
    RDrev runtimeBytecode g s0 ∨
      ((calldataWord I.calldata 4).toNat < _root_.EVM.addressModulus ∧
       ∃ k' C', RD runtimeBytecode I g s0 ret (calldataWord I.calldata 4 :: rest)
         mem aw rdata acc k' C') := by
  have guard := runtime_run reached with [jumpdest, push0, push1 ⟨32⟩,
    dup3, dup5, sub, slt, iszero, push2 ⟨1347⟩]
  by_cases accepted : UInt256.isZero (UInt256.slt
      (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩) = ⟨0⟩
  · have rejected := runtime_run guard with [jumpiNT accepted, push0, dup1]
    exact .inl (rejected.rev 0 (by decide +kernel)
      (fun s _ stack => memExpRevert0 s stack) (by evm_ov))
  · have entered := runtime_run guard with [
      jumpiT accepted
        (jumpScan_valid runtimeBytecode 1347 1360 (by decide +kernel)),
      jumpdest, dup2, calldataload, push2 ⟨1358⟩, dup2, push2 ⟨1165⟩,
      jump (jumpScan_valid runtimeBytecode 1165 1180 (by decide +kernel))]
    by_cases canonical : (calldataWord I.calldata 4).toNat < _root_.EVM.addressModulus
    ·
      obtain ⟨_, _, checked⟩ := runtime_address_check (calldataWord I.calldata 4) ⟨1358⟩
        (calldataWord I.calldata 4 :: ⟨0⟩ :: ⟨4⟩ :: UInt256.ofNat I.calldata.size :: ret :: rest)
        canonical (jumpScan_valid runtimeBytecode 1358 1370 (by decide +kernel))
        (by simp only [List.length_cons]; omega) entered
      exact .inr ⟨canonical, _, _, runtime_run checked with [jumpdest, swap4, swap3, pop, pop, pop, jump destination]⟩
    · exact .inl (runtime_address_check_reject (calldataWord I.calldata 4) ⟨1358⟩
        (calldataWord I.calldata 4 :: ⟨0⟩ :: ⟨4⟩ :: UInt256.ofNat I.calldata.size :: ret :: rest)
        canonical (by simp only [List.length_cons]; omega) entered)

end Rollup.EVM
