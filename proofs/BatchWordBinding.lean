import proofs.BatchSourceChecks
import proofs.BatchBytecodeExecution
import proofs.BatchBytecodeMaps
import proofs.DepositAgreement

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Rollup.EVM

/-- Bind the source batch to the seven words read by the bytecode. -/
structure BatchWordBinding (I : ExecutionEnv) (batch : Batch) : Prop where
  number : batch.number = (calldataWord I.calldata 4).toNat
  oldRoot : (⟨batch.oldRoot⟩ : UInt256) = calldataWord I.calldata 36
  newRoot : (⟨batch.newRoot⟩ : UInt256) = calldataWord I.calldata 68
  depositOwner : UInt256.ofNat batch.depositOwner.val = calldataWord I.calldata 100
  depositAmount : batch.depositAmount = (calldataWord I.calldata 132).toNat
  withdrawalOwner : UInt256.ofNat batch.withdrawalOwner.val = calldataWord I.calldata 164
  withdrawalAmount : batch.withdrawalAmount = (calldataWord I.calldata 196).toNat

def batchFromCalldata (I : ExecutionEnv) : Batch :=
  ⟨(calldataWord I.calldata 4).toNat, (calldataWord I.calldata 36).val,
    (calldataWord I.calldata 68).val, AccountAddress.ofNat (calldataWord I.calldata 100).toNat,
    (calldataWord I.calldata 132).toNat, AccountAddress.ofNat (calldataWord I.calldata 164).toNat,
    (calldataWord I.calldata 196).toNat⟩

/-- Canonical address words give a bound source batch. ABI decoding is separate. -/
theorem batch_word_binding (I : ExecutionEnv)
    (depositCanonical : (calldataWord I.calldata 100).toNat < _root_.EVM.addressModulus)
    (withdrawalCanonical : (calldataWord I.calldata 164).toNat < _root_.EVM.addressModulus) :
    BatchWordBinding I (batchFromCalldata I) := by
  constructor
  · rfl
  · rfl
  · rfl
  · have word := keyValueToWord_address_of_canonical _ depositCanonical
    rw [keyValueToWord_address] at word
    exact word
  · rfl
  · have word := keyValueToWord_address_of_canonical _ withdrawalCanonical
    rw [keyValueToWord_address] at word
    exact word
  · rfl

/-- The source and bytecode use the same deposit mapping slot. -/
theorem batch_deposit_slot_binding {I : ExecutionEnv} {batch : Batch}
    (binding : BatchWordBinding I batch) : keySlot (.pending batch.depositOwner) = batchDepositSlot I := by
  simp only [keySlot, mapSlot, keyValueToWord_address, batchDepositSlot, solcMappingSlot,
    binding.depositOwner]

/-- The source and bytecode use the same withdrawal mapping slot. -/
theorem batch_claim_slot_binding {I : ExecutionEnv} {batch : Batch}
    (binding : BatchWordBinding I batch) : keySlot (.claims batch.withdrawalOwner) = batchClaimSlot I := by
  simp only [keySlot, mapSlot, keyValueToWord_address, batchClaimSlot, solcMappingSlot,
    binding.withdrawalOwner]

end Rollup.EVM
