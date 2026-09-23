import proofs.BatchAcceptedEquivalence
import proofs.BatchSourceTotal

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 100000
set_option maxHeartbeats 200000

namespace Rollup.EVM

/-- Decoded batches have equivalent outcomes, including failed checks and out-of-gas. -/
theorem batch_decoded_equivalence {cA gh bl σ σ_solm σ₀ A I} {g : UInt256}
    (code : I.code = runtimeBytecode) (writable : I.perm = true)
    (bounded : I.calldata.size < UInt256.size)
    (selector : solcSelectorWord I = ⟨0x88af9950⟩) (maps : accountMapEquiv σ σ_solm)
    (length : 228 ≤ I.calldata.size) (signedBound : I.calldata.size < 2 ^ 255 + 4)
    (depositCanonical : (calldataWord I.calldata 100).toNat < _root_.EVM.addressModulus)
    (withdrawalCanonical : (calldataWord I.calldata 164).toNat < _root_.EVM.addressModulus) :
    runtimeEquivalenceFor config contract cA gh bl σ σ_solm σ₀ g A I := by
  by_cases checks : BatchBytecodeChecks σ I
  · exact batch_checked_equivalence code writable bounded selector maps checks
  · let initial := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    have binding := batch_word_binding I depositCanonical withdrawalCanonical
    have failed : ¬ BatchExecutionChecks initial (batchFromCalldata I) := by
      intro sourceChecks
      have byteChecks := batch_checks_to_bytecode initial (batchFromCalldata I) binding
        length signedBound depositCanonical withdrawalCanonical sourceChecks
      exact checks ((batch_checks_equiv I maps).mpr byteChecks)
    have source := batch_source_rejected initial (batchFromCalldata I) failed
    have dispatched := source_selector_dispatch I ⟨1, by decide⟩ (by omega) selector
    have decoded := batch_abi_decode I length signedBound depositCanonical withdrawalCanonical
    have rejected : RDrev runtimeBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
      rcases batch_bytecode_classification (cA := cA) (gh := gh) (bl := bl)
          (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g)
          code writable bounded selector with rejected | ⟨accepted, _⟩
      · exact rejected
      · exact (checks accepted).elim
    have equivalent := rejected.reEquivExecutionRevert code dispatched decoded source
    simpa [Sat256.ofUInt256, Sat256.toUInt256] using equivalent

/-- The writable batch entry matches the source for all calldata and rejection paths. -/
theorem batch_correct {cA gh bl σ σ_solm σ₀ A I} {g : UInt256}
    (code : I.code = runtimeBytecode) (writable : I.perm = true)
    (four : 4 ≤ I.calldata.size) (bounded : I.calldata.size < UInt256.size)
    (selector : solcSelectorWord I = ⟨0x88af9950⟩) (maps : accountMapEquiv σ σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ σ_solm σ₀ g A I := by
  by_cases valid : 228 ≤ I.calldata.size ∧ I.calldata.size < 2 ^ 255 + 4 ∧
      (calldataWord I.calldata 100).toNat < _root_.EVM.addressModulus ∧
      (calldataWord I.calldata 164).toNat < _root_.EVM.addressModulus
  · exact batch_decoded_equivalence code writable bounded selector maps
      valid.1 valid.2.1 valid.2.2.1 valid.2.2.2
  · have rejected : RDrev runtimeBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
      rcases batch_bytecode_classification (cA := cA) (gh := gh) (bl := bl)
          (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g)
          code writable bounded selector with rejected | ⟨checks, _⟩
      · exact rejected
      · exact (valid ⟨checks.length, checks.signedBound, checks.depositCanonical,
          checks.withdrawalCanonical⟩).elim
    have dispatched := source_selector_dispatch I ⟨1, by decide⟩ four selector
    have decoded := batch_abi_rejected I valid
    have equivalent := rejected.reEquivDecodingFailed (σ_solm := σ_solm) (cfg := config)
      code dispatched decoded
    simpa [Sat256.ofUInt256, Sat256.toUInt256] using equivalent

end Rollup.EVM
