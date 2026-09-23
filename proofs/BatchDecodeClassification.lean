import proofs.RuntimeBatchDecode

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Rollup.EVM

/-- The batch decoder rejects or returns seven words with canonical addresses. -/
theorem batch_decode_classification {I : ExecutionEnv} {g : Sat256} {s0 : Ethereum.State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (ret : UInt256) (rest : List UInt256)
    (four : 4 ≤ I.calldata.size) (bounded : I.calldata.size < UInt256.size)
    (destination : (D_J runtimeBytecode 0).contains ret = true)
    (space : rest.length + 17 ≤ 1024)
    (reached : RD runtimeBytecode I g s0 ⟨1188⟩
      (⟨4⟩ :: UInt256.ofNat I.calldata.size :: ret :: rest) mem aw rdata acc k C) :
    RDrev runtimeBytecode g s0 ∨
      (228 ≤ I.calldata.size ∧ I.calldata.size < 2 ^ 255 + 4 ∧
       (calldataWord I.calldata 100).toNat < _root_.EVM.addressModulus ∧
       (calldataWord I.calldata 164).toNat < _root_.EVM.addressModulus ∧
       ∃ k' C', RD runtimeBytecode I g s0 ret (batchDecodedStack I rest)
         mem aw rdata acc k' C') := by
  by_cases length : 228 ≤ I.calldata.size
  · by_cases signedBound : I.calldata.size < 2 ^ 255 + 4
    · obtain ⟨_, _, first⟩ := batch_decode_first ret rest length signedBound bounded (by omega) reached
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
          exact Or.inr ⟨length, signedBound, canonicalFirst, canonicalSecond,
            batch_decode_tail ret rest (by omega) destination secondChecked⟩
        · exact Or.inl (runtime_address_check_reject _ _ (batchSecondRest I ret rest)
            canonicalSecond (by simp only [batchSecondRest, List.length_cons]; omega) second)
      · exact Or.inl (runtime_address_check_reject _ _ (batchFirstRest I ret rest)
          canonicalFirst (by simp only [batchFirstRest, List.length_cons]; omega) first)
    · exact Or.inl (batch_decode_bad_length ret rest (by omega)
        (solcCalldataStaticLenCheckHuge (words := 7) (by omega) bounded (by decide +kernel)) reached)
  · exact Or.inl (batch_decode_bad_length ret rest (by omega)
      (solcCalldataStaticLenCheckShort (words := 7) four (by omega) bounded (by decide +kernel)) reached)

end Rollup.EVM
