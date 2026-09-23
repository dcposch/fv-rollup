import proofs.RuntimeBatchDecode

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Rollup.EVM

/-- Classify the batch decoder without a calldata-size premise. -/
theorem batch_decode_any {I : ExecutionEnv} {g : Sat256} {s0 : Ethereum.State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (ret : UInt256) (rest : List UInt256)
    (destination : (D_J runtimeBytecode 0).contains ret = true)
    (space : rest.length + 17 ≤ 1024)
    (reached : RD runtimeBytecode I g s0 ⟨1188⟩
      (⟨4⟩ :: UInt256.ofNat I.calldata.size :: ret :: rest) mem aw rdata acc k C) :
    RDrev runtimeBytecode g s0 ∨
      ((calldataWord I.calldata 100).toNat < _root_.EVM.addressModulus ∧
       (calldataWord I.calldata 164).toNat < _root_.EVM.addressModulus ∧
       ∃ k' C', RD runtimeBytecode I g s0 ret (batchDecodedStack I rest)
         mem aw rdata acc k' C') := by
  have guard := runtime_run reached with [jumpdest, push0, dup1, push0, dup1, push0, dup1,
    push0, push1 ⟨224⟩, dup9, dup11, sub, slt, iszero, push2 ⟨1210⟩]
  by_cases accepted : UInt256.isZero (UInt256.slt
      (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨224⟩) = ⟨0⟩
  · have rejected := runtime_run guard with [jumpiNT accepted, push0, dup1]
    exact .inl (rejected.rev 0 (by decide +kernel)
      (fun s _ stack => memExpRevert0 s stack) (by evm_ov))
  · have first := runtime_run guard with [jumpiT accepted
      (jumpScan_valid runtimeBytecode 1210 1260 (by decide +kernel)), jumpdest,
      dup8, calldataload, swap7, pop, push1 ⟨32⟩, dup9, add, calldataload, swap6, pop,
      push1 ⟨64⟩, dup9, add, calldataload, swap5, pop,
      push1 ⟨96⟩, dup9, add, calldataload, push2 ⟨1242⟩, dup2, push2 ⟨1165⟩,
      jump (jumpScan_valid runtimeBytecode 1165 1180 (by decide +kernel))]
    by_cases canonicalFirst : (calldataWord I.calldata 100).toNat < _root_.EVM.addressModulus
    · obtain ⟨_, _, firstChecked⟩ := runtime_address_check (calldataWord I.calldata 100) ⟨1242⟩
        (batchFirstRest I ret rest) canonicalFirst
        (jumpScan_valid runtimeBytecode 1242 1270 (by decide +kernel))
        (by simp only [batchFirstRest, List.length_cons]; omega) first
      obtain ⟨_, _, second⟩ := batch_decode_second ret rest (by omega) firstChecked
      by_cases canonicalSecond : (calldataWord I.calldata 164).toNat < _root_.EVM.addressModulus
      · obtain ⟨_, _, secondChecked⟩ := runtime_address_check (calldataWord I.calldata 164) ⟨1265⟩
          (batchSecondRest I ret rest) canonicalSecond
          (jumpScan_valid runtimeBytecode 1265 1290 (by decide +kernel))
          (by simp only [batchSecondRest, List.length_cons]; omega) second
        exact Or.inr ⟨canonicalFirst, canonicalSecond,
          batch_decode_tail ret rest (by omega) destination secondChecked⟩
      · exact Or.inl (runtime_address_check_reject _ _ (batchSecondRest I ret rest)
          canonicalSecond (by simp only [batchSecondRest, List.length_cons]; omega) second)
    · exact Or.inl (runtime_address_check_reject _ _ (batchFirstRest I ret rest)
        canonicalFirst (by simp only [batchFirstRest, List.length_cons]; omega) first)

end Rollup.EVM
