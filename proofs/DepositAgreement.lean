import proofs.DepositCorrespondence
import proofs.DepositBodyChecks

open Solm Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Rollup.EVM

theorem deposit_address_word_inj {a b : Address} :
    UInt256.ofNat a.val = UInt256.ofNat b.val ↔ a = b := by
  constructor
  · intro same
    apply Fin.ext
    have words := congrArg UInt256.toNat same
    rw [ulit_toNat' _ (lt_trans a.isLt (by decide : 2 ^ 160 < UInt256.size)),
      ulit_toNat' _ (lt_trans b.isLt (by decide : 2 ^ 160 < UInt256.size))] at words
    exact words
  · rintro rfl
    rfl

/-- Equivalent account maps give the same deposit checks. -/
theorem deposit_checks_init {cA gh bl σ σ_solm σ₀ A I} {g : Sat256} (owner : Address)
    (maps : accountMapEquiv σ σ_solm) :
    DepositExecutionChecks (initState cA gh bl σ_solm σ₀ g A I) owner ↔
      (solcSlotWord σ I ⟨6⟩ = ⟨0⟩ ∧ UInt256.ofNat owner.val ≠ ⟨0⟩ ∧
       UInt256.ofNat I.codeOwner.val ≠ UInt256.ofNat owner.val ∧ I.weiValue ≠ ⟨0⟩ ∧
       I.weiValue.toNat + (solcSlotWord (sstoreAccountMap I.codeOwner σ ⟨6⟩ ⟨1⟩) I
         (solcMappingSlot ⟨4⟩ (UInt256.ofNat owner.val))).toNat < UInt256.size) := by
  have lockEq : solcSlotWord σ I ⟨6⟩ = solcSlotWord σ_solm I ⟨6⟩ :=
    accountMapEquiv_storage_findD maps I.codeOwner ⟨6⟩ ⟨0⟩
  have creditEq : solcSlotWord (sstoreAccountMap I.codeOwner σ ⟨6⟩ ⟨1⟩) I
      (solcMappingSlot ⟨4⟩ (UInt256.ofNat owner.val)) =
      solcSlotWord (sstoreAccountMap I.codeOwner σ_solm ⟨6⟩ ⟨1⟩) I
        (solcMappingSlot ⟨4⟩ (UInt256.ofNat owner.val)) :=
    accountMapEquiv_storage_findD
      (accountMapEquiv_sstoreAccountMap I.codeOwner ⟨6⟩ ⟨1⟩ maps) I.codeOwner _ ⟨0⟩
  have zero : UInt256.ofNat owner.val ≠ (⟨0⟩ : UInt256) ↔ owner ≠ 0 := by
    change UInt256.ofNat owner.val ≠ UInt256.ofNat (0 : Address).val ↔ owner ≠ 0
    exact not_congr deposit_address_word_inj
  have different : UInt256.ofNat I.codeOwner.val ≠ UInt256.ofNat owner.val ↔
      I.codeOwner ≠ owner := not_congr (deposit_address_word_inj (a := I.codeOwner) (b := owner))
  change (solcSlotWord σ_solm I ⟨6⟩ = ⟨0⟩ ∧ owner ≠ 0 ∧ owner ≠ I.codeOwner ∧
    I.weiValue ≠ ⟨0⟩ ∧ depositExecutionCredit (initState cA gh bl σ_solm σ₀ g A I) owner < wordLimit) ↔ _
  rw [deposit_execution_credit_init, ← creditEq, ← lockEq, zero,
    different, ne_comm (a := I.codeOwner), Nat.add_comm]
  rfl

end Rollup.EVM
