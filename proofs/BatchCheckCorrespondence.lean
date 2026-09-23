import proofs.BatchStorageCorrespondence

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 100000
set_option maxHeartbeats 200000
-- This syntax linter unfolds symbolic calldata guards. Kernel checks remain active.
set_option linter.constructorNameAsVariable false

namespace Rollup.EVM

/-- Typed optional owners and their address words give the same checks. -/
theorem batch_optional_owner_binding (I : ExecutionEnv) (owner : Address) (amount : Nat)
    (ownerWord amountWord : UInt256)
    (ownerBinding : UInt256.ofNat owner.val = ownerWord) (amountBinding : amount = amountWord.toNat) :
    (if amount = 0 then owner = 0 else owner ≠ 0 ∧ owner ≠ I.codeOwner) ↔
    (if amountWord = ⟨0⟩ then ownerWord = ⟨0⟩
      else ownerWord ≠ ⟨0⟩ ∧ UInt256.ofNat I.codeOwner.val ≠ ownerWord) := by
  have empty : amount = 0 ↔ amountWord = ⟨0⟩ := by
    rw [amountBinding]
    exact ⟨uint256_toNat_eq_zero, fun zero => by rw [zero]; rfl⟩
  have zeroOwner : UInt256.ofNat owner.val = (⟨0⟩ : UInt256) ↔ owner = 0 := by
    change UInt256.ofNat owner.val = UInt256.ofNat (0 : Address).val ↔ owner = 0
    exact deposit_address_word_inj
  rw [← ownerBinding]
  by_cases zero : amount = 0
  · rw [if_pos zero, if_pos (empty.mp zero)]
    exact zeroOwner.symm
  · rw [if_neg zero, if_neg (fun h => zero (empty.mpr h))]
    constructor
    · rintro ⟨nonzero, different⟩
      exact ⟨(not_congr zeroOwner).mpr nonzero,
        fun same => different (deposit_address_word_inj.mp same).symm⟩
    · rintro ⟨nonzero, different⟩
      exact ⟨(not_congr zeroOwner).mp nonzero,
        fun same => different (deposit_address_word_inj.mpr same.symm)⟩

/-- Source authorization and the masked bytecode caller check agree. -/
theorem batch_authorization_correspondence (evm : Ethereum.State) :
    Value.address evm.executionEnv.source = getterValue evm .sequencer ↔
      UInt256.ofNat evm.executionEnv.source.val =
        UInt256.land (solcSlotWord evm.accountMap evm.executionEnv ⟨0⟩) solcAddrMask := by
  constructor
  · intro authorized
    have same : evm.executionEnv.source = AccountAddress.ofNat
        (UInt256.land (solcSlotWord evm.accountMap evm.executionEnv ⟨0⟩) solcAddrMask).toNat :=
      Value.address.inj authorized
    rw [same]
    have word := keyValueToWord_address_of_canonical _
      (solcAddrMask_result_canonical (solcSlotWord evm.accountMap evm.executionEnv ⟨0⟩))
    rw [keyValueToWord_address] at word
    exact word
  · intro authorized
    have same := solcMaskedAddress_eq_source_of_word_eq (I := evm.executionEnv) authorized.symm
    change Value.address evm.executionEnv.source = Value.address
      (AccountAddress.ofNat (UInt256.land (solcSlotWord evm.accountMap evm.executionEnv ⟨0⟩) solcAddrMask).toNat)
    rw [same]

/-- Passed bytecode checks imply every source check for the bound batch. -/
theorem batch_checks_to_source (evm : Ethereum.State) (batch : Batch)
    (binding : BatchWordBinding evm.executionEnv batch)
    (checks : BatchBytecodeChecks evm.accountMap evm.executionEnv) :
    BatchExecutionChecks evm batch := by
  have depositCovered : batch.depositAmount ≤ batchDepositCredit evm batch := by
    rw [binding.depositAmount, batch_credit_correspondence evm batch binding]
    exact checks.depositCovered
  have backingFits : batchAvailable evm batch < wordLimit := by
    rw [batch_available_correspondence evm batch binding depositCovered]
    exact checks.backingFits
  have available : (batchAvailableWord evm.accountMap evm.executionEnv).toNat = batchAvailable evm batch := by
    rw [← batch_available_word_correspondence evm batch binding depositCovered backingFits,
      ulit_toNat' _ backingFits]
  have withdrawalCovered : batch.withdrawalAmount ≤ batchAvailable evm batch := by
    rw [binding.withdrawalAmount, ← available]
    exact checks.withdrawalCovered
  have claimFits : batchNextCredit evm batch < wordLimit := by
    rw [batch_claim_correspondence evm batch binding depositCovered backingFits withdrawalCovered]
    exact checks.claimFits
  have depositOwner : if batch.depositAmount = 0 then batch.depositOwner = 0
      else batch.depositOwner ≠ 0 ∧ batch.depositOwner ≠ evm.executionEnv.codeOwner := by
    apply (batch_optional_owner_binding evm.executionEnv batch.depositOwner batch.depositAmount
      _ _ binding.depositOwner binding.depositAmount).mpr
    with_reducible exact checks.depositOwner
  have withdrawalOwner : if batch.withdrawalAmount = 0 then batch.withdrawalOwner = 0
      else batch.withdrawalOwner ≠ 0 ∧ batch.withdrawalOwner ≠ evm.executionEnv.codeOwner := by
    apply (batch_optional_owner_binding evm.executionEnv batch.withdrawalOwner batch.withdrawalAmount
      _ _ binding.withdrawalOwner binding.withdrawalAmount).mpr
    with_reducible exact checks.withdrawalOwner
  exact {
    nonpayable := checks.nonpayable
    unlocked := checks.unlocked
    authorized := (batch_authorization_correspondence evm).mpr checks.authorized
    numberFits := checks.numberFits
    nextNumber := binding.number.trans checks.nextNumber
    oldRoot := congrArg UInt256.val (binding.oldRoot.trans checks.oldRoot)
    depositOwner := depositOwner
    withdrawalOwner := withdrawalOwner
    depositCovered := depositCovered
    backingFits := backingFits
    withdrawalCovered := withdrawalCovered
    claimFits := claimFits }

/-- Source checks imply all bytecode checks once argument decoding has passed. -/
theorem batch_checks_to_bytecode (evm : Ethereum.State) (batch : Batch)
    (binding : BatchWordBinding evm.executionEnv batch)
    (length : 228 ≤ evm.executionEnv.calldata.size)
    (signedBound : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (depositCanonical : (calldataWord evm.executionEnv.calldata 100).toNat < _root_.EVM.addressModulus)
    (withdrawalCanonical : (calldataWord evm.executionEnv.calldata 164).toNat < _root_.EVM.addressModulus)
    (checks : BatchExecutionChecks evm batch) :
    BatchBytecodeChecks evm.accountMap evm.executionEnv := by
  have header : BatchPrefixChecks evm.accountMap evm.executionEnv := {
    nonpayable := checks.nonpayable
    length := length
    signedBound := signedBound
    depositCanonical := depositCanonical
    withdrawalCanonical := withdrawalCanonical
    unlocked := checks.unlocked
    authorized := (batch_authorization_correspondence evm).mp checks.authorized
    numberFits := checks.numberFits
    nextNumber := binding.number.symm.trans checks.nextNumber
    oldRoot := by
      rw [← binding.oldRoot, checks.oldRoot]
      rfl }
  have depositComparison := batch_optional_owner_binding evm.executionEnv batch.depositOwner batch.depositAmount
    _ _ binding.depositOwner binding.depositAmount
  have withdrawalComparison := batch_optional_owner_binding evm.executionEnv batch.withdrawalOwner batch.withdrawalAmount
    _ _ binding.withdrawalOwner binding.withdrawalAmount
  constructor
  · constructor
    · exact header
    · with_reducible exact depositComparison.mp checks.depositOwner
    · with_reducible exact withdrawalComparison.mp checks.withdrawalOwner
    · change (calldataWord evm.executionEnv.calldata 132).toNat ≤
        (batchInputCredit evm.accountMap evm.executionEnv).toNat
      rw [← binding.depositAmount, ← batch_credit_correspondence evm batch binding]
      exact checks.depositCovered
  · rw [← batch_available_correspondence evm batch binding checks.depositCovered]
    exact checks.backingFits
  · rw [← binding.withdrawalAmount,
      ← batch_available_word_correspondence evm batch binding checks.depositCovered checks.backingFits,
      ulit_toNat' _ checks.backingFits]
    exact checks.withdrawalCovered
  · rw [← batch_claim_correspondence evm batch binding checks.depositCovered checks.backingFits checks.withdrawalCovered]
    exact checks.claimFits

end Rollup.EVM
