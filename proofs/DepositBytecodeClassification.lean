import proofs.DepositBytecodeExecution
import proofs.DepositBytecodeReject
import proofs.RuntimeDecodeReject
import proofs.RuntimeOverflow

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Rollup.EVM

/-- Every deposit call rejects or has the checked deposit effect.
    Both alternatives permit out-of-gas. -/
theorem deposit_bytecode_classification {cA gh bl σ σ₀ A I} {g : Sat256}
    (code : I.code = runtimeBytecode) (writable : I.perm = true)
    (bounded : I.calldata.size < UInt256.size)
    (selector : solcSelectorWord I = ⟨0xf340fa01⟩) :
    let owner := calldataWord I.calldata 4
    let slot := solcMappingSlot ⟨4⟩ owner
    let locked := sstoreAccountMap I.codeOwner σ ⟨6⟩ ⟨1⟩
    let credit := solcSlotWord locked I slot
    RDrev runtimeBytecode g (initState cA gh bl σ σ₀ g A I) ∨
      (36 ≤ I.calldata.size ∧ I.calldata.size < 2 ^ 255 + 4 ∧
       owner.toNat < _root_.EVM.addressModulus ∧ owner ≠ ⟨0⟩ ∧
       UInt256.ofNat I.codeOwner.val ≠ owner ∧ I.weiValue ≠ ⟨0⟩ ∧
       solcSlotWord σ I ⟨6⟩ = ⟨0⟩ ∧ I.weiValue.toNat + credit.toNat < UInt256.size ∧
       RDret runtimeBytecode g (initState cA gh bl σ σ₀ g A I)
         (cA, sstoreAccountMap I.codeOwner
           (sstoreAccountMap I.codeOwner locked slot (I.weiValue + credit)) ⟨6⟩ ⟨0⟩)
         ByteArray.empty) := by
  dsimp only
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
          by_cases unlocked : solcSlotWord σ I ⟨6⟩ = ⟨0⟩
          · obtain ⟨_, _, locked⟩ := deposit_bytecode_enter _ (by evm_ov) writable unlocked entered
            by_cases nonzero : calldataWord I.calldata 4 ≠ ⟨0⟩
            · by_cases notSelf : UInt256.ofNat I.codeOwner.val ≠ calldataWord I.calldata 4
              · obtain ⟨_, _, ownerChecked⟩ := deposit_bytecode_owner_ok _ _ (by evm_ov)
                  canonical nonzero notSelf locked
                by_cases value : I.weiValue ≠ ⟨0⟩
                · obtain ⟨_, _, valueChecked⟩ := deposit_bytecode_value_ok _ (by evm_ov) value ownerChecked
                  obtain ⟨_, _, loaded⟩ := deposit_bytecode_load _ _ (by evm_ov) canonical (by decide +kernel) valueChecked
                  by_cases fits : I.weiValue.toNat +
                      (solcSlotWord (sstoreAccountMap I.codeOwner σ ⟨6⟩ ⟨1⟩) I
                        (solcMappingSlot ⟨4⟩ (calldataWord I.calldata 4))).toNat < UInt256.size
                  · exact Or.inr ⟨length, signedBound, canonical, nonzero, notSelf, value, unlocked, fits,
                      deposit_bytecode_execution code writable length signedBound bounded selector
                        canonical nonzero notSelf value unlocked fits⟩
                  · exact Or.inl (runtime_checked_add_overflow _ _ _ _ (by evm_ov) (by omega) loaded)
                · exact Or.inl (deposit_bytecode_zero_value _ (by evm_ov) (not_ne_iff.mp value) ownerChecked)
              · exact Or.inl (deposit_bytecode_self_owner _ _ (by evm_ov) canonical nonzero
                  (not_ne_iff.mp notSelf) locked)
            · rw [not_ne_iff.mp nonzero] at locked
              exact Or.inl (deposit_bytecode_zero_owner _ (by evm_ov) locked)
          · exact Or.inl (deposit_bytecode_locked _ (by evm_ov) unlocked entered)
        · exact Or.inl (runtime_address_bad_word _ _ length signedBound bounded canonical (by evm_ov) dispatched)
      · exact Or.inl (runtime_address_bad_length _ _ (by evm_ov)
          (solcDecodeLenCheckHuge_4_32 (by omega) bounded) dispatched)
    · exact Or.inl (runtime_address_bad_length _ _ (by evm_ov)
        (solcDecodeLenCheckShort_4_32 four (by omega) bounded) dispatched)
  · exact Or.inl (runtime_short_calldata code (by omega))

end Rollup.EVM
