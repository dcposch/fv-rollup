import proofs.DepositBytecodeClassification

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Rollup.EVM

/-- An accepted EVM deposit passed every check and has the exact storage effect. -/
theorem deposit_xi_success {cA gh bl σ σ₀ A I} {g : UInt256}
    {cA' σ' gas substate output}
    (code : I.code = runtimeBytecode) (writable : I.perm = true)
    (bounded : I.calldata.size < UInt256.size)
    (selector : solcSelectorWord I = ⟨0xf340fa01⟩)
    (success : Ξ cA gh bl σ σ₀ g A I = .ok (.success (cA', σ', gas, substate) output)) :
    let owner := calldataWord I.calldata 4
    let slot := solcMappingSlot ⟨4⟩ owner
    let locked := sstoreAccountMap I.codeOwner σ ⟨6⟩ ⟨1⟩
    let credit := solcSlotWord locked I slot
    36 ≤ I.calldata.size ∧ I.calldata.size < 2 ^ 255 + 4 ∧
    owner.toNat < _root_.EVM.addressModulus ∧ owner ≠ ⟨0⟩ ∧
    UInt256.ofNat I.codeOwner.val ≠ owner ∧ I.weiValue ≠ ⟨0⟩ ∧
    solcSlotWord σ I ⟨6⟩ = ⟨0⟩ ∧ I.weiValue.toNat + credit.toNat < UInt256.size ∧
    cA' = cA ∧ σ' = sstoreAccountMap I.codeOwner
      (sstoreAccountMap I.codeOwner locked slot (I.weiValue + credit)) ⟨6⟩ ⟨0⟩ ∧
    output = ByteArray.empty := by
  have classified := deposit_bytecode_classification (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) code writable bounded selector
  rcases classified with rejected | ⟨length, signedBound, canonical, nonzero, notSelf,
    value, unlocked, fits, returned⟩
  · rcases rejected with outOfGas | ⟨_, _, reverted⟩
    · have impossible := Xi_error_of_X (g := g) (by
        rw [← code] at outOfGas
        simpa [Sat256.ofUInt256] using outOfGas)
      rw [success] at impossible
      cases impossible
    · have impossible := Xi_revert_of_X (g := g) (by
        rw [← code] at reverted
        simpa [Sat256.ofUInt256] using reverted)
      rw [success] at impossible
      cases impossible
  · rcases returned with outOfGas | ⟨finalState, result, accounts⟩
    · have impossible := Xi_error_of_X (g := g) (by
        rw [← code] at outOfGas
        simpa [Sat256.ofUInt256] using outOfGas)
      rw [success] at impossible
      cases impossible
    · have actual := Xi_success_of_X (g := g) (by
        rw [← code] at result
        simpa [Sat256.ofUInt256] using result)
      rw [success] at actual
      cases actual
      exact ⟨length, signedBound, canonical, nonzero, notSelf, value, unlocked, fits,
        congrArg Prod.fst accounts, congrArg Prod.snd accounts, rfl⟩

end Rollup.EVM
