import proofs.DepositBytecodeGuards
import proofs.RuntimeDecodeReject

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Rollup.EVM

/-- Every deposit selector rejects while the lock is set, for all calldata. -/
theorem deposit_locked_reject {cA gh bl σ σ₀ A I} {g : Sat256}
    (code : I.code = runtimeBytecode) (bounded : I.calldata.size < UInt256.size)
    (selector : solcSelectorWord I = ⟨0xf340fa01⟩)
    (locked : solcSlotWord σ I ⟨6⟩ ≠ ⟨0⟩) :
    RDrev runtimeBytecode g (initState cA gh bl σ σ₀ g A I) := by
  by_cases four : 4 ≤ I.calldata.size
  · obtain ⟨_, _, dispatched⟩ := runtime_deposit_dispatch (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (g := g) code four bounded selector
    by_cases length : 36 ≤ I.calldata.size
    · by_cases signedBound : I.calldata.size < 2 ^ 255 + 4
      · by_cases canonical : (calldataWord I.calldata 4).toNat < _root_.EVM.addressModulus
        · obtain ⟨_, _, decoded⟩ := runtime_address_decode ⟨393⟩ [⟨226⟩, ⟨0xf340fa01⟩]
            length signedBound bounded canonical
            (jumpScan_valid runtimeBytecode 393 410 (by decide +kernel)) (by evm_ov) dispatched
          have entered := runtime_run decoded with [jumpdest, push2 ⟨1045⟩,
            jump (jumpScan_valid runtimeBytecode 1045 1060 (by decide +kernel))]
          exact deposit_bytecode_locked _ (by evm_ov) locked entered
        · exact runtime_address_bad_word _ _ length signedBound bounded canonical (by evm_ov) dispatched
      · exact runtime_address_bad_length _ _ (by evm_ov)
          (solcDecodeLenCheckHuge_4_32 (by omega) bounded) dispatched
    · exact runtime_address_bad_length _ _ (by evm_ov)
        (solcDecodeLenCheckShort_4_32 four (by omega) bounded) dispatched
  · exact runtime_short_calldata code (by omega)

end Rollup.EVM
