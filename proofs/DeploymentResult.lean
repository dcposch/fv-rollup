import proofs.Deployment

open Ethereum Ethereum.EVM Reasoning.Theory

namespace Rollup.EVM

/-- The constructor writes the sequencer and root before code installation. -/
noncomputable def Deployment.writtenAccounts (d : Deployment) (sequencer : Address) (root : Root) :
    AccountMap :=
  let code := creationBytecode ++ creationArgs (UInt256.ofNat sequencer.val) ⟨root⟩
  let self := d.address code
  let accounts := d.initialAccounts code
  sstoreAccountMap self (sstoreAccountMap self accounts ⟨0⟩
    (packedAddress (accounts.find? self |>.option ⟨0⟩
      (fun account => account.storage.findD ⟨0⟩ ⟨0⟩)) (UInt256.ofNat sequencer.val))) ⟨1⟩ ⟨root⟩

/-- Accepted deployment has the exact constructor writes and installed code. -/
theorem deployment_success_accounts (d : Deployment) (sequencer : Address) (root : Root)
    (nonzero : sequencer ≠ 0)
    (fresh : d.fresh (creationBytecode ++ creationArgs (UInt256.ofNat sequencer.val) ⟨root⟩))
    {address created accounts gas substate data}
    (deployed : d.run (creationBytecode ++ creationArgs (UInt256.ofNat sequencer.val) ⟨root⟩) =
      (address, created, accounts, gas, substate, true, data)) :
    address = d.address (creationBytecode ++ creationArgs (UInt256.ofNat sequencer.val) ⟨root⟩) ∧
      accounts = (d.writtenAccounts sequencer root).insert address
        { (d.writtenAccounts sequencer root).findD address default with code := runtimeBytecode } ∧
      data = ByteArray.empty := by
  let code := creationBytecode ++ creationArgs (UInt256.ofNat sequencer.val) ⟨root⟩
  have canonical : (UInt256.ofNat sequencer.val).toNat < _root_.EVM.addressModulus := by
    rw [address_word_toNat]
    exact sequencer.isLt
  have wordNonzero : UInt256.ofNat sequencer.val ≠ ⟨0⟩ := by
    intro same
    apply nonzero
    apply Fin.ext
    have sameNat := congrArg UInt256.toNat same
    simpa only [address_word_toNat] using sameNat
  have execution := creation_xi_packed
    (cA := d.created.insert (d.address code)) (gh := d.genesis) (bl := d.blocks)
    (σ := d.initialAccounts code) (σ₀ := d.original)
    (A := d.substate.addAccessedAccount (d.address code)) (g := d.gas)
    (I := d.initialEnv code) (UInt256.ofNat sequencer.val) ⟨root⟩
    canonical wordNonzero rfl rfl rfl
  rcases execution with outOfGas | ⟨gasLeft, substateAfter, initialized⟩
  · have failed := deployment_outOfGas d code fresh outOfGas
    rw [deployed] at failed
    simp only [Prod.mk.injEq] at failed
    simp_all
  · have result := deployment_install_result d code fresh _ _ gasLeft substateAfter initialized
    rw [deployed] at result
    split at result
    · simp only [Prod.mk.injEq] at result
      simp_all
    · have addressEq := congrArg Prod.fst result
      have accountsEq := congrArg (fun output => output.2.2.1) result
      have dataEq := congrArg (fun output => output.2.2.2.2.2.2) result
      dsimp only at addressEq accountsEq dataEq
      refine ⟨addressEq, ?_, dataEq⟩
      rw [addressEq]
      exact accountsEq

end Rollup.EVM
