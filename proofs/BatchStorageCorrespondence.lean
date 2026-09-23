import proofs.BatchWordBinding

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Rollup.EVM

private theorem read_map (evm : Ethereum.State) (I : ExecutionEnv) (slot : UInt256) :
    readWord evm I.codeOwner slot = solcSlotWord evm.accountMap I slot := rfl

/-- Both implementations read the same deposit credit after locking. -/
theorem batch_credit_correspondence (evm : Ethereum.State) (batch : Batch)
    (binding : BatchWordBinding evm.executionEnv batch) :
    batchDepositCredit evm batch = (batchInputCredit evm.accountMap evm.executionEnv).toNat := by
  simp only [batchDepositCredit, batchLockedState, read_map, storageStore_accountMap,
    batch_deposit_slot_binding binding, batchInputCredit, batchDepositWord]

/-- A covered debit has the same account map in both implementations. -/
theorem batch_debit_correspondence (evm : Ethereum.State) (batch : Batch)
    (binding : BatchWordBinding evm.executionEnv batch)
    (covered : batch.depositAmount ≤ batchDepositCredit evm batch) :
    (batchDebitedState evm batch).accountMap = batchAfterDeposit evm.accountMap evm.executionEnv := by
  have word : UInt256.ofNat (batchDepositCredit evm batch - batch.depositAmount) =
      UInt256.sub (batchInputCredit evm.accountMap evm.executionEnv)
        (calldataWord evm.executionEnv.calldata 132) := by
    apply u256_inj
    have bound : batchDepositCredit evm batch - batch.depositAmount < UInt256.size := by
      rw [batch_credit_correspondence evm batch binding]
      exact lt_of_le_of_lt (Nat.sub_le _ _) (batchInputCredit evm.accountMap evm.executionEnv).val.isLt
    rw [ulit_toNat' _ bound, usub_toNat (by
      rw [← binding.depositAmount, ← batch_credit_correspondence evm batch binding]
      exact covered)]
    rw [batch_credit_correspondence evm batch binding, binding.depositAmount]
  simp only [batchDebitedState, batchLockedState, storageStore_accountMap,
    batch_deposit_slot_binding binding, word, batchAfterDeposit, batchDepositWrite]

/-- The source backing sum is the sum used by checked bytecode addition. -/
theorem batch_available_correspondence (evm : Ethereum.State) (batch : Batch)
    (binding : BatchWordBinding evm.executionEnv batch)
    (covered : batch.depositAmount ≤ batchDepositCredit evm batch) :
    batchAvailable evm batch = (calldataWord evm.executionEnv.calldata 132).toNat +
      (solcSlotWord (batchAfterDeposit evm.accountMap evm.executionEnv) evm.executionEnv ⟨3⟩).toNat := by
  simp only [batchAvailable, read_map, batch_debit_correspondence evm batch binding covered,
    binding.depositAmount, Nat.add_comm]

/-- Bounded addition gives the same available backing word. -/
theorem batch_available_word_correspondence (evm : Ethereum.State) (batch : Batch)
    (binding : BatchWordBinding evm.executionEnv batch)
    (covered : batch.depositAmount ≤ batchDepositCredit evm batch)
    (fits : batchAvailable evm batch < wordLimit) :
    UInt256.ofNat (batchAvailable evm batch) = batchAvailableWord evm.accountMap evm.executionEnv := by
  apply u256_inj
  rw [ulit_toNat' _ fits, batchAvailableWord, uadd_toNat,
    ← batch_available_correspondence evm batch binding covered, Nat.mod_eq_of_lt (show batchAvailable evm batch < UInt256.size from fits)]

/-- Covered backing subtraction gives the same account map. -/
theorem batch_backing_correspondence (evm : Ethereum.State) (batch : Batch)
    (binding : BatchWordBinding evm.executionEnv batch)
    (depositCovered : batch.depositAmount ≤ batchDepositCredit evm batch)
    (fits : batchAvailable evm batch < wordLimit)
    (withdrawalCovered : batch.withdrawalAmount ≤ batchAvailable evm batch) :
    (batchBackedState evm batch).accountMap = batchAfterBacking evm.accountMap evm.executionEnv := by
  have available := batch_available_word_correspondence evm batch binding depositCovered fits
  have word : UInt256.ofNat (batchAvailable evm batch - batch.withdrawalAmount) =
      UInt256.sub (batchAvailableWord evm.accountMap evm.executionEnv)
        (calldataWord evm.executionEnv.calldata 196) := by
    rw [← available]
    apply u256_inj
    rw [ulit_toNat' _ (lt_of_le_of_lt (Nat.sub_le _ _) fits),
      usub_toNat (by rw [ulit_toNat' _ fits, ← binding.withdrawalAmount]; exact withdrawalCovered),
      ulit_toNat' _ fits, binding.withdrawalAmount]
  simp only [batchBackedState, storageStore_accountMap,
    batch_debit_correspondence evm batch binding depositCovered, word, batchAfterBacking, batchBackingWrite]

/-- The source claim sum is the sum used by checked bytecode addition. -/
theorem batch_claim_correspondence (evm : Ethereum.State) (batch : Batch)
    (binding : BatchWordBinding evm.executionEnv batch)
    (depositCovered : batch.depositAmount ≤ batchDepositCredit evm batch)
    (fits : batchAvailable evm batch < wordLimit)
    (withdrawalCovered : batch.withdrawalAmount ≤ batchAvailable evm batch) :
    batchNextCredit evm batch = (calldataWord evm.executionEnv.calldata 196).toNat +
      (solcSlotWord (batchAfterBacking evm.accountMap evm.executionEnv) evm.executionEnv
        (batchClaimSlot evm.executionEnv)).toNat := by
  simp only [batchNextCredit, read_map, batch_claim_slot_binding binding,
    batch_backing_correspondence evm batch binding depositCovered fits withdrawalCovered,
    binding.withdrawalAmount, Nat.add_comm]

/-- All seven source writes produce the exact bytecode account map. -/
theorem batch_accounts_correspondence (evm : Ethereum.State) (batch : Batch)
    (binding : BatchWordBinding evm.executionEnv batch) (checks : BatchExecutionChecks evm batch) :
    (batchExecutionState evm batch).accountMap = batchOutputAccounts evm.accountMap evm.executionEnv := by
  have claim : UInt256.ofNat (batchNextCredit evm batch) = batchNextClaim evm.accountMap evm.executionEnv := by
    apply u256_inj
    rw [ulit_toNat' _ checks.claimFits, batchNextClaim, uadd_toNat,
      ← batch_claim_correspondence evm batch binding checks.depositCovered checks.backingFits checks.withdrawalCovered,
      Nat.mod_eq_of_lt (show batchNextCredit evm batch < UInt256.size from checks.claimFits)]
  have number : UInt256.ofNat batch.number = calldataWord evm.executionEnv.calldata 4 := by
    rw [binding.number, u256_ofNat_toNat]
  simp only [batchExecutionState, batchNumberedState, batchRootedState, batchCreditedState,
    storageStore_accountMap,
    batch_backing_correspondence evm batch binding checks.depositCovered checks.backingFits checks.withdrawalCovered,
    batch_claim_slot_binding binding, claim, binding.newRoot, number, batchOutputAccounts, batchFinalWrite]

end Rollup.EVM
