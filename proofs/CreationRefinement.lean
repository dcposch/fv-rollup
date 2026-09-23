import proofs.CreationABI

open Solm Ethereum Reasoning.Theory Reasoning.Reach

namespace Rollup.EVM

theorem address_word_toNat (address : Address) :
    (UInt256.ofNat address.val).toNat = address.val :=
  ulit_toNat' _ (lt_trans address.isLt (by decide : 2 ^ 160 < UInt256.size))

/-- The full constructor matches the source for typed arguments and equivalent account maps. -/
theorem constructor_equivalence_for {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (sequencer : Address) (root : Root) (writable : I.perm = true)
    (maps : accountMapEquiv σ_evm σ_solm)
    (code : I.code = creationBytecode ++ creationArgs (UInt256.ofNat sequencer.val) ⟨root⟩) :
    constructorEquivalenceFor config contract [.address sequencer, rootValue root]
      cA gh bl σ_evm σ_solm σ₀ g A I runtimeBytecode := by
  by_cases value : I.weiValue = ⟨0⟩
  · by_cases zero : sequencer = 0
    · subst sequencer
      have execution := creation_execution_zero (cA := cA) (gh := gh) (bl := bl)
        (σ := σ_evm) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) ⟨root⟩ value code
      rcases execution.xiResult code with outOfGas | ⟨gas, bytes, reverted⟩
      · exact .outOfGas (by simpa [Sat256.ofUInt256] using outOfGas)
      · exact .execution (by simpa [Sat256.ofUInt256] using reverted)
          (constructor_solm_zero root value) (.revert rfl rfl)
    · have canonical : (UInt256.ofNat sequencer.val).toNat < _root_.EVM.addressModulus := by
        rw [address_word_toNat]
        exact sequencer.isLt
      have nonzero : UInt256.ofNat sequencer.val ≠ ⟨0⟩ := by
        intro equal
        apply zero
        apply Fin.ext
        have same := congrArg UInt256.toNat equal
        simpa only [address_word_toNat] using same
      rcases creation_xi_packed (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
        (σ₀ := σ₀) (A := A) (g := g) (UInt256.ofNat sequencer.val) ⟨root⟩
        canonical nonzero writable value code with outOfGas | ⟨gas, substate, success⟩
      · exact .outOfGas outOfGas
      · refine .execution success (constructor_solm_success sequencer root zero value)
          (.success rfl rfl ?_ ?_ rfl)
        · simp only [constructorPackedState, storageStore_createdAccounts, initState]
        · simp only [constructorPackedState, storageStore_accountMap,
            initState, readWord, Solm.EVM.storageLoad, Ethereum.State.lookupAccount]
          rw [accountMapEquiv_storage_findD maps I.codeOwner ⟨0⟩ ⟨0⟩]
          exact accountMapEquiv_sstoreAccountMap I.codeOwner ⟨1⟩ ⟨root⟩
            (accountMapEquiv_sstoreAccountMap I.codeOwner ⟨0⟩ _ maps)
  · have execution := creation_nonpayable (cA := cA) (gh := gh) (bl := bl)
      (σ := σ_evm) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) _ code value
    rcases execution.xiResult code with outOfGas | ⟨gas, bytes, reverted⟩
    · exact .outOfGas (by simpa [Sat256.ofUInt256] using outOfGas)
    · exact .execution (by simpa [Sat256.ofUInt256] using reverted)
        (constructor_solm_nonpayable sequencer root value) (.revert rfl rfl)

/-- The pinned creation bytecode matches the source constructor. -/
theorem constructor_correct : constructorEquivalence config creationBytecode contract runtimeBytecode := by
  refine .intro ?_
  intro cA gh bl σ_evm σ_solm σ₀ g A I args deployed encoded code _calldata writable maps
  obtain ⟨sequencer, root, rfl, deployedCode⟩ := creation_deployment_shape encoded
  exact constructor_equivalence_for sequencer root writable maps (code.trans deployedCode)

end Rollup.EVM
