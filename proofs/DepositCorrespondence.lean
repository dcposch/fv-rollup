import proofs.Deposit
import proofs.DepositBytecodeSuccess

open Solm Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Rollup.EVM

theorem deposit_slot (owner : Address) :
    keySlot (.pending owner) = solcMappingSlot ⟨4⟩ (UInt256.ofNat owner.val) := by
  simp only [keySlot, mapSlot, keyValueToWord_address, solcMappingSlot]

theorem deposit_execution_credit_init {cA gh bl σ σ₀ A I} {g : Sat256} (owner : Address) :
    depositExecutionCredit (initState cA gh bl σ σ₀ g A I) owner =
      (solcSlotWord (sstoreAccountMap I.codeOwner σ ⟨6⟩ ⟨1⟩) I
        (solcMappingSlot ⟨4⟩ (UInt256.ofNat owner.val))).toNat + I.weiValue.toNat := by
  simp only [depositExecutionCredit, readWord, Solm.EVM.storageLoad,
    Ethereum.State.lookupAccount, storageStore_accountMap, initState, deposit_slot,
    solcSlotWord]
  rfl

/-- An accepted bytecode deposit has a matching source execution.
    The source can use an equivalent account map. No slot separation is required. -/
theorem deposit_success_correspondence {cA gh bl σ σ_solm σ₀ A I} {g : UInt256}
    {cA' σ' gas substate output} (owner : Address)
    (code : I.code = runtimeBytecode) (writable : I.perm = true)
    (bounded : I.calldata.size < UInt256.size)
    (selector : solcSelectorWord I = ⟨0xf340fa01⟩)
    (decoded : calldataWord I.calldata 4 = UInt256.ofNat owner.val)
    (maps : accountMapEquiv σ σ_solm)
    (success : Ξ cA gh bl σ σ₀ g A I = .ok (.success (cA', σ', gas, substate) output)) :
    let initial := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    let finalState := depositExecutionState initial owner
    ∃ frame, ExecTransitionBody config contract initial (depositLocals owner)
      contract.transitions[0]!.body (.returned frame finalState none) ∧
      cA' = finalState.createdAccounts ∧ accountMapEquiv σ' finalState.accountMap ∧
      output = ByteArray.empty := by
  obtain ⟨_, _, _, nonzeroWord, differentWord, value, unlocked, fits, created, accounts, outputEq⟩ :=
    deposit_xi_success code writable bounded selector success
  rw [decoded] at nonzeroWord differentWord fits accounts
  let initial := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have lockEq : solcSlotWord σ I ⟨6⟩ = solcSlotWord σ_solm I ⟨6⟩ :=
    accountMapEquiv_storage_findD maps I.codeOwner ⟨6⟩ ⟨0⟩
  have lockedMaps := accountMapEquiv_sstoreAccountMap I.codeOwner ⟨6⟩ ⟨1⟩ maps
  have creditEq : solcSlotWord (sstoreAccountMap I.codeOwner σ ⟨6⟩ ⟨1⟩) I
      (solcMappingSlot ⟨4⟩ (UInt256.ofNat owner.val)) =
      solcSlotWord (sstoreAccountMap I.codeOwner σ_solm ⟨6⟩ ⟨1⟩) I
        (solcMappingSlot ⟨4⟩ (UInt256.ofNat owner.val)) :=
    accountMapEquiv_storage_findD lockedMaps I.codeOwner _ ⟨0⟩
  have initialUnlocked : readWord initial I.codeOwner ⟨6⟩ = ⟨0⟩ := lockEq.symm.trans unlocked
  have nonzero : owner ≠ 0 := by
    intro zero
    apply nonzeroWord
    subst owner
    rfl
  have different : owner ≠ I.codeOwner := by
    intro self
    apply differentWord
    rw [self]
  have creditBound : depositExecutionCredit initial owner < wordLimit := by
    rw [deposit_execution_credit_init]
    rw [creditEq] at fits
    exact Nat.add_comm _ _ ▸ fits
  have sumWord : I.weiValue + solcSlotWord (sstoreAccountMap I.codeOwner σ ⟨6⟩ ⟨1⟩) I
      (solcMappingSlot ⟨4⟩ (UInt256.ofNat owner.val)) =
      UInt256.ofNat (depositExecutionCredit initial owner) := by
    apply u256_inj
    rw [uadd_toNat, ulit_toNat' _ creditBound, deposit_execution_credit_init, creditEq]
    rw [creditEq] at fits
    rw [Nat.mod_eq_of_lt fits, Nat.add_comm]
  have source := (exact_function (deposit_body_exact initial owner initialUnlocked
    nonzero different value creditBound)).1
  refine ⟨_, source, ?_, ?_, outputEq⟩
  · simpa only [depositExecutionState, storageStore_createdAccounts, initState] using created
  · rw [accounts, sumWord]
    simp only [depositExecutionState, storageStore_accountMap, initial, initState, deposit_slot]
    exact accountMapEquiv_sstoreAccountMap I.codeOwner ⟨6⟩ ⟨0⟩
      (accountMapEquiv_sstoreAccountMap I.codeOwner _ _ lockedMaps)

end Rollup.EVM
