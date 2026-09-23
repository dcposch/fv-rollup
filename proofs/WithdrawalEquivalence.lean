import proofs.WithdrawalCheckedEquivalence

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 100000
set_option maxHeartbeats 200000

namespace Rollup.EVM

/-- Decoded withdrawals have equivalent outcomes, including failed checks and out-of-gas. -/
theorem withdrawal_decoded_equivalence {cA gh bl σ σ_solm σ₀ A I} {g : UInt256}
    (code : I.code = runtimeBytecode) (writable : I.perm = true)
    (bounded : I.calldata.size < UInt256.size)
    (selector : solcSelectorWord I = ⟨0xbb3ef682⟩) (maps : accountMapEquiv σ σ_solm)
    (length : 68 ≤ I.calldata.size) (signedBound : I.calldata.size < 2 ^ 255 + 4)
    (canonical : (calldataWord I.calldata 4).toNat < _root_.EVM.addressModulus) :
    runtimeEquivalenceFor config contract cA gh bl σ σ_solm σ₀ g A I := by
  by_cases checks : WithdrawalBytecodeChecks σ I
  · exact withdrawal_checked_equivalence code writable bounded selector maps checks
  · let initial := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    let owner := withdrawalOwnerFromCalldata I
    let amount := (calldataWord I.calldata 36).toNat
    have binding : UInt256.ofNat owner.val = calldataWord I.calldata 4 := by
      have same := keyValueToWord_address_of_canonical _ canonical
      rw [keyValueToWord_address] at same
      exact same
    have failed : ¬ WithdrawalExecutionChecks initial owner amount := by
      intro sourceChecks
      have byteChecks := withdrawal_checks_to_bytecode initial owner amount binding rfl
        length signedBound canonical sourceChecks
      exact checks ((withdrawal_checks_equiv I maps).mpr byteChecks)
    have source := withdrawal_body_rejected_checks initial owner amount failed
    have dispatched := source_selector_dispatch I ⟨2, by decide⟩ (by omega) selector
    have decoded := withdrawal_abi_decode I length signedBound canonical
    have rejected : RDrev runtimeBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
      rcases withdrawal_bytecode_classification (cA := cA) (gh := gh) (bl := bl)
          (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g)
          code writable bounded selector with rejected | ⟨accepted, _⟩
      · exact rejected
      · exact (checks accepted).elim
    have equivalent := rejected.reEquivExecutionRevert code dispatched decoded source
    simpa [Sat256.ofUInt256, Sat256.toUInt256] using equivalent

/-- The writable withdrawal entry matches the source for all calldata and rejection paths. -/
theorem withdrawal_correct {cA gh bl σ σ_solm σ₀ A I} {g : UInt256}
    (code : I.code = runtimeBytecode) (writable : I.perm = true)
    (four : 4 ≤ I.calldata.size) (bounded : I.calldata.size < UInt256.size)
    (selector : solcSelectorWord I = ⟨0xbb3ef682⟩) (maps : accountMapEquiv σ σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ σ_solm σ₀ g A I := by
  by_cases valid : 68 ≤ I.calldata.size ∧ I.calldata.size < 2 ^ 255 + 4 ∧
      (calldataWord I.calldata 4).toNat < _root_.EVM.addressModulus
  · exact withdrawal_decoded_equivalence code writable bounded selector maps
      valid.1 valid.2.1 valid.2.2
  · have rejected : RDrev runtimeBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
      rcases withdrawal_bytecode_classification (cA := cA) (gh := gh) (bl := bl)
          (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g)
          code writable bounded selector with rejected | ⟨checks, _⟩
      · exact rejected
      · exact (valid ⟨checks.length, checks.signedBound, checks.canonical⟩).elim
    have dispatched := source_selector_dispatch I ⟨2, by decide⟩ four selector
    have decoded := withdrawal_abi_rejected I valid
    have equivalent := rejected.reEquivDecodingFailed (σ_solm := σ_solm) (cfg := config)
      code dispatched decoded
    simpa [Sat256.ofUInt256, Sat256.toUInt256] using equivalent

end Rollup.EVM
