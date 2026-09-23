import proofs.WithdrawalBytecodePrelude

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Rollup.EVM

/-- A writable withdrawal rejects or reaches payment setup with the lock set and credit saved. -/
theorem withdrawal_bytecode_prelude {cA gh bl σ σ₀ A I} {g : Sat256}
    (code : I.code = runtimeBytecode) (writable : I.perm = true)
    (bounded : I.calldata.size < UInt256.size)
    (selector : solcSelectorWord I = ⟨0xbb3ef682⟩) :
    RDrev runtimeBytecode g (initState cA gh bl σ σ₀ g A I) ∨
      (WithdrawalBytecodeChecks σ I ∧
        ∃ k C, RD runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨908⟩
          [withdrawalClaimWord (sstoreAccountMap I.codeOwner σ ⟨6⟩ ⟨1⟩) I,
            calldataWord I.calldata 36, calldataWord I.calldata 4, ⟨226⟩, ⟨0xbb3ef682⟩]
          (twoWordHashMem (calldataWord I.calldata 4) ⟨5⟩ solcFreePtrMem) (UInt256.ofNat 3)
          ByteArray.empty (cA, sstoreAccountMap I.codeOwner σ ⟨6⟩ ⟨1⟩) k C) := by
  rcases withdrawal_entry_classification (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (g := g) code bounded selector with
    rejected | ⟨nonpayable, length, signedBound, canonical, _, _, entry⟩
  · exact .inl rejected
  · by_cases unlocked : solcSlotWord σ I ⟨6⟩ = ⟨0⟩
    · obtain ⟨_, _, entered⟩ := withdrawal_bytecode_enter _ (by simp) writable unlocked entry
      rcases withdrawal_bytecode_amount _ _ [⟨226⟩, ⟨0xbb3ef682⟩] (by decide) entered with
        ⟨rejected, _⟩ | ⟨positive, _, _, checkedAmount⟩
      · exact .inl rejected
      · obtain ⟨_, _, loaded⟩ := withdrawal_bytecode_credit_load _ (by decide) canonical
          solcFreePtrMem_size checkedAmount
        rcases withdrawal_bytecode_credit_check _ _ _ [⟨226⟩, ⟨0xbb3ef682⟩] (by decide) loaded with
          ⟨rejected, _⟩ | ⟨covered, _, _, checkedCredit⟩
        · exact .inl rejected
        · exact .inr ⟨⟨nonpayable, length, signedBound, canonical, unlocked, positive, covered⟩,
            _, _, checkedCredit⟩
    · exact .inl (withdrawal_bytecode_locked _ (by simp) unlocked entry)

/-- Every accepted writable withdrawal passed the checks before payment. -/
theorem withdrawal_xi_prelude_checks {cA gh bl σ σ₀ A I} {g : Sat256}
    {cA' σ' gas substate output} (code : I.code = runtimeBytecode) (writable : I.perm = true)
    (bounded : I.calldata.size < UInt256.size)
    (selector : solcSelectorWord I = ⟨0xbb3ef682⟩)
    (success : Ξ cA gh bl σ σ₀ g.toUInt256 A I = .ok (.success (cA', σ', gas, substate) output)) :
    WithdrawalBytecodeChecks σ I := by
  rcases withdrawal_bytecode_prelude (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (g := g) code writable bounded selector with
    rejected | ⟨checks, _⟩
  · rcases rejected.xiResult code with failed | ⟨gas', data, actual⟩
    · rw [success] at failed
      cases failed
    · rw [success] at actual
      cases actual
  · exact checks

end Rollup.EVM
