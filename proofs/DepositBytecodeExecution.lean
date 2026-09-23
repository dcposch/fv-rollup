import proofs.DepositBytecodeBody
import proofs.RuntimeDecode

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Rollup.EVM

/-- A valid deposit writes its credit, releases the lock, and returns no data.
    This result permits out-of-gas. It does not assert that execution succeeds. -/
theorem deposit_bytecode_execution {cA gh bl σ σ₀ A I} {g : Sat256}
    (code : I.code = runtimeBytecode) (writable : I.perm = true)
    (length : 36 ≤ I.calldata.size) (signedBound : I.calldata.size < 2 ^ 255 + 4)
    (bounded : I.calldata.size < UInt256.size)
    (selector : solcSelectorWord I = ⟨0xf340fa01⟩)
    (canonical : (calldataWord I.calldata 4).toNat < _root_.EVM.addressModulus)
    (nonzero : calldataWord I.calldata 4 ≠ ⟨0⟩)
    (notSelf : UInt256.ofNat I.codeOwner.val ≠ calldataWord I.calldata 4)
    (value : I.weiValue ≠ ⟨0⟩)
    (unlocked : solcSlotWord σ I ⟨6⟩ = ⟨0⟩)
    (fits : I.weiValue.toNat +
      (solcSlotWord (sstoreAccountMap I.codeOwner σ ⟨6⟩ ⟨1⟩) I
        (solcMappingSlot ⟨4⟩ (calldataWord I.calldata 4))).toNat < UInt256.size) :
    RDret runtimeBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner (sstoreAccountMap I.codeOwner σ ⟨6⟩ ⟨1⟩)
          (solcMappingSlot ⟨4⟩ (calldataWord I.calldata 4))
          (I.weiValue + solcSlotWord (sstoreAccountMap I.codeOwner σ ⟨6⟩ ⟨1⟩) I
            (solcMappingSlot ⟨4⟩ (calldataWord I.calldata 4)))) ⟨6⟩ ⟨0⟩)
      ByteArray.empty := by
  obtain ⟨_, _, dispatched⟩ := runtime_deposit_dispatch (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) code (by omega) bounded selector
  obtain ⟨_, _, decoded⟩ := runtime_address_decode ⟨393⟩ [⟨226⟩, ⟨0xf340fa01⟩]
    length signedBound bounded canonical
    (jumpScan_valid runtimeBytecode 393 410 (by decide +kernel)) (by evm_ov) dispatched
  have entered := runtime_run decoded with [jumpdest, push2 ⟨1045⟩,
    jump (jumpScan_valid runtimeBytecode 1045 1060 (by decide +kernel))]
  obtain ⟨_, _, locked⟩ := deposit_bytecode_enter _ (by evm_ov) writable unlocked entered
  obtain ⟨_, _, ownerChecked⟩ := deposit_bytecode_owner_ok _ _ (by evm_ov)
    canonical nonzero notSelf locked
  obtain ⟨_, _, valueChecked⟩ := deposit_bytecode_value_ok _ (by evm_ov) value ownerChecked
  obtain ⟨_, _, loaded⟩ := deposit_bytecode_load _ _ (by evm_ov) canonical (by decide +kernel) valueChecked
  obtain ⟨_, _, added⟩ := runtime_checked_add _ _ ⟨1153⟩ _ (by evm_ov) fits
    (jumpScan_valid runtimeBytecode 1153 1170 (by decide +kernel)) loaded
  obtain ⟨_, _, stored⟩ := deposit_bytecode_store _ _ _ _ ⟨226⟩ _ (by evm_ov) writable
    (jumpScan_valid runtimeBytecode 226 240 (by decide +kernel)) added
  exact (runtime_run stored with [jumpdest]).stop (by decide +kernel) (by evm_ov)

end Rollup.EVM
