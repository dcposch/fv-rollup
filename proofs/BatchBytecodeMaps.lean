import proofs.BatchBytecodeClassification

open Solm Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
-- This syntax linter unfolds symbolic calldata guards. Kernel checks remain active.
set_option linter.constructorNameAsVariable false

namespace Rollup.EVM

/-- Equivalent account maps have the same credit after locking. -/
theorem batch_input_credit_equiv {σ τ : AccountMap} (I : ExecutionEnv)
    (maps : accountMapEquiv σ τ) : batchInputCredit σ I = batchInputCredit τ I := by
  exact accountMapEquiv_storage_findD
    (accountMapEquiv_sstoreAccountMap I.codeOwner ⟨6⟩ ⟨1⟩ maps) I.codeOwner (batchDepositSlot I) ⟨0⟩

/-- The deposit debit preserves account-map equivalence. -/
theorem batch_deposit_accounts_equiv {σ τ : AccountMap} (I : ExecutionEnv)
    (maps : accountMapEquiv σ τ) : accountMapEquiv (batchAfterDeposit σ I) (batchAfterDeposit τ I) := by
  change accountMapEquiv
    (sstoreAccountMap I.codeOwner (sstoreAccountMap I.codeOwner σ ⟨6⟩ ⟨1⟩)
      (batchDepositSlot I) (UInt256.sub (batchInputCredit σ I) (calldataWord I.calldata 132)))
    (sstoreAccountMap I.codeOwner (sstoreAccountMap I.codeOwner τ ⟨6⟩ ⟨1⟩)
      (batchDepositSlot I) (UInt256.sub (batchInputCredit τ I) (calldataWord I.calldata 132)))
  rw [batch_input_credit_equiv I maps]
  exact accountMapEquiv_sstoreAccountMap I.codeOwner _ _
    (accountMapEquiv_sstoreAccountMap I.codeOwner ⟨6⟩ ⟨1⟩ maps)

/-- Equivalent account maps give the same available backing word. -/
theorem batch_available_equiv {σ τ : AccountMap} (I : ExecutionEnv)
    (maps : accountMapEquiv σ τ) : batchAvailableWord σ I = batchAvailableWord τ I := by
  unfold batchAvailableWord
  rw [show solcSlotWord (batchAfterDeposit σ I) I ⟨3⟩ = solcSlotWord (batchAfterDeposit τ I) I ⟨3⟩ from
    accountMapEquiv_storage_findD (batch_deposit_accounts_equiv I maps) I.codeOwner ⟨3⟩ ⟨0⟩]

/-- The backing write preserves account-map equivalence. -/
theorem batch_backing_accounts_equiv {σ τ : AccountMap} (I : ExecutionEnv)
    (maps : accountMapEquiv σ τ) : accountMapEquiv (batchAfterBacking σ I) (batchAfterBacking τ I) := by
  unfold batchAfterBacking batchBackingWrite
  rw [batch_available_equiv I maps]
  exact accountMapEquiv_sstoreAccountMap I.codeOwner _ _ (batch_deposit_accounts_equiv I maps)

/-- Equivalent account maps give the same new withdrawal credit. -/
theorem batch_claim_equiv {σ τ : AccountMap} (I : ExecutionEnv)
    (maps : accountMapEquiv σ τ) : batchNextClaim σ I = batchNextClaim τ I := by
  unfold batchNextClaim
  rw [show solcSlotWord (batchAfterBacking σ I) I (batchClaimSlot I) =
      solcSlotWord (batchAfterBacking τ I) I (batchClaimSlot I) from
    accountMapEquiv_storage_findD (batch_backing_accounts_equiv I maps) I.codeOwner (batchClaimSlot I) ⟨0⟩]

/-- All seven batch writes preserve account-map equivalence. -/
theorem batch_output_accounts_equiv {σ τ : AccountMap} (I : ExecutionEnv)
    (maps : accountMapEquiv σ τ) : accountMapEquiv (batchOutputAccounts σ I) (batchOutputAccounts τ I) := by
  unfold batchOutputAccounts batchFinalWrite
  rw [batch_claim_equiv I maps]
  apply accountMapEquiv_sstoreAccountMap
  apply accountMapEquiv_sstoreAccountMap
  apply accountMapEquiv_sstoreAccountMap
  exact accountMapEquiv_sstoreAccountMap I.codeOwner _ _ (batch_backing_accounts_equiv I maps)

private theorem batch_checks_transfer {σ τ : AccountMap} (I : ExecutionEnv)
    (maps : accountMapEquiv σ τ) (checks : BatchBytecodeChecks σ I) : BatchBytecodeChecks τ I := by
  have slots (slot : UInt256) : solcSlotWord σ I slot = solcSlotWord τ I slot :=
    accountMapEquiv_storage_findD maps I.codeOwner slot ⟨0⟩
  have credit := batch_input_credit_equiv I maps
  have backing : solcSlotWord (batchAfterDeposit σ I) I ⟨3⟩ =
      solcSlotWord (batchAfterDeposit τ I) I ⟨3⟩ :=
    accountMapEquiv_storage_findD (batch_deposit_accounts_equiv I maps) I.codeOwner ⟨3⟩ ⟨0⟩
  have available := batch_available_equiv I maps
  have claim : solcSlotWord (batchAfterBacking σ I) I (batchClaimSlot I) =
      solcSlotWord (batchAfterBacking τ I) I (batchClaimSlot I) :=
    accountMapEquiv_storage_findD (batch_backing_accounts_equiv I maps) I.codeOwner (batchClaimSlot I) ⟨0⟩
  have headerChecks : BatchPrefixChecks τ I := by
    exact {
      nonpayable := checks.nonpayable
      length := checks.length
      signedBound := checks.signedBound
      depositCanonical := checks.depositCanonical
      withdrawalCanonical := checks.withdrawalCanonical
      unlocked := (slots ⟨6⟩).symm.trans checks.unlocked
      authorized := by rw [← slots ⟨0⟩]; exact checks.authorized
      numberFits := by rw [← slots ⟨2⟩]; exact checks.numberFits
      nextNumber := by rw [← slots ⟨2⟩]; exact checks.nextNumber
      oldRoot := by rw [← slots ⟨1⟩]; exact checks.oldRoot }
  constructor
  · constructor
    · exact headerChecks
    · with_reducible exact checks.depositOwner
    · with_reducible exact checks.withdrawalOwner
    · change (calldataWord I.calldata 132).toNat ≤ (batchInputCredit τ I).toNat
      rw [← credit]
      exact checks.depositCovered
  · rw [← backing]; exact checks.backingFits
  · rw [← available]; exact checks.withdrawalCovered
  · rw [← claim]; exact checks.claimFits

/-- Equivalent account maps give the same batch checks. -/
theorem batch_checks_equiv {σ τ : AccountMap} (I : ExecutionEnv)
    (maps : accountMapEquiv σ τ) : BatchBytecodeChecks σ I ↔ BatchBytecodeChecks τ I :=
  ⟨batch_checks_transfer I maps, batch_checks_transfer I maps.symm⟩

end Rollup.EVM
