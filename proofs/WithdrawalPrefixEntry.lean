import proofs.WithdrawalPrefixDecode

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Rollup.EVM

/-- A prefix to a child must pass the short-calldata guard. -/
theorem runtime_prefix_four {I : ExecutionEnv} {target child : Ethereum.State}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (start : PCR runtimeBytecode I target child ⟨0⟩ [] ByteArray.empty ⟨0⟩ ByteArray.empty (cA, σ)) :
    4 ≤ I.calldata.size := by
  by_contra small
  have entered := runtime_prefix_prologue start
  have rejected := runtime_run entered with [push1 ⟨4⟩, calldatasize, lt, push2 ⟨132⟩,
    jumpiT (lt_four_ne_zero_of_lt (by omega)) (jumpScan_valid runtimeBytecode 132 140 (by decide +kernel)),
    jumpdest, push0, dup1]
  exact rejected.halt (arg := none) (by decide +kernel) (Or.inr (Or.inr (Or.inl rfl)))

/-- A withdrawal prefix passes the value and ABI checks before its body. -/
theorem withdrawal_prefix_entry {I : ExecutionEnv} {target child : Ethereum.State}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (four : 4 ≤ I.calldata.size) (bounded : I.calldata.size < UInt256.size)
    (dispatched : PCR runtimeBytecode I target child ⟨284⟩ [⟨0xbb3ef682⟩]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ)) :
    I.weiValue = ⟨0⟩ ∧ 68 ≤ I.calldata.size ∧ I.calldata.size < 2 ^ 255 + 4 ∧
      (calldataWord I.calldata 4).toNat < _root_.EVM.addressModulus ∧
      PCR runtimeBytecode I target child ⟨843⟩
        [calldataWord I.calldata 36, calldataWord I.calldata 4, ⟨226⟩, ⟨0xbb3ef682⟩]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) := by
  have guard := runtime_run dispatched with [jumpdest, callvalue, dup1, iszero, push2 ⟨295⟩]
  have value : I.weiValue = ⟨0⟩ := by
    by_contra nonzero
    have rejected := runtime_run guard with [jumpiNT (isZero_eq_zero_of_ne nonzero), push0, dup1]
    exact rejected.halt (arg := none) (by decide +kernel) (Or.inr (Or.inr (Or.inl rfl)))
  have decoder := runtime_run guard with [
    jumpiT (by rw [value]; decide) (jumpScan_valid runtimeBytecode 295 320 (by decide +kernel)),
    jumpdest, pop, push2 ⟨226⟩, push2 ⟨310⟩, calldatasize, push1 ⟨4⟩, push2 ⟨1289⟩,
    jump (jumpScan_valid runtimeBytecode 1289 1310 (by decide +kernel))]
  have length : 68 ≤ I.calldata.size := by
    by_contra short
    exact withdrawal_prefix_decode_bad_length _ _ (by decide)
      (solcDecodeLenCheckShort_4_64 four (by omega) bounded) decoder
  have signedBound : I.calldata.size < 2 ^ 255 + 4 := by
    by_contra large
    exact withdrawal_prefix_decode_bad_length _ _ (by decide)
      (solcDecodeLenCheckHuge_4_64 (by omega) bounded) decoder
  have canonical : (calldataWord I.calldata 4).toNat < _root_.EVM.addressModulus := by
    by_contra malformed
    exact withdrawal_prefix_decode_bad_owner _ _ length signedBound bounded malformed (by decide) decoder
  have decoded := withdrawal_prefix_decode ⟨310⟩ [⟨226⟩, ⟨0xbb3ef682⟩]
    length signedBound bounded canonical
    (jumpScan_valid runtimeBytecode 310 340 (by decide +kernel)) (by decide) decoder
  exact ⟨value, length, signedBound, canonical, runtime_run decoded with
    [jumpdest, push2 ⟨843⟩, jump (jumpScan_valid runtimeBytecode 843 880 (by decide +kernel))]⟩

end Rollup.EVM
