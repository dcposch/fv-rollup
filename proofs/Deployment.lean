import semantics.Deployment
import proofs.CreationRefinement

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Rollup.EVM

theorem deployment_collision_free (d : Deployment) (code : ByteArray) (fresh : d.fresh code) :
    ((d.accounts.findD (d.address code) default).nonce ≠ ⟨0⟩ ||
      (d.accounts.findD (d.address code) default).code.size ≠ 0 ||
      (d.accounts.findD (d.address code) default).storage != default) = false := by
  obtain ⟨nonce, bytes, storage⟩ := fresh
  simp [nonce, bytes, storage]
  decide

theorem deployment_code_free (d : Deployment) (code : ByteArray) (fresh : d.fresh code) :
    (match d.accounts.find? (d.address code) with
      | some account => decide (account.code ≠ ByteArray.empty ∨ account.nonce ≠ ⟨0⟩)
      | none => false) = false := by
  cases found : d.accounts.find? (d.address code) with
  | none => rfl
  | some account =>
    simp only [Deployment.fresh, Batteries.RBMap.findD, found, Option.getD_some] at fresh
    simp [fresh.1, fresh.2.1]

/-- Code deposit either fails for gas or installs the exact returned runtime bytes. -/
theorem deployment_install_result (d : Deployment) (code : ByteArray) (fresh : d.fresh code)
    (created : Batteries.RBSet AccountAddress compare) (accounts : AccountMap)
    (gas : UInt256) (substate : Substate)
    (initialized : d.initialize code = .ok (.success (created, accounts, gas, substate) runtimeBytecode)) :
    d.run code =
      if gas.toNat < 285800 then
        (d.address code, created, d.accounts, ⟨0⟩,
          d.substate.addAccessedAccount (d.address code), false, ByteArray.empty)
      else
        (d.address code, created,
          accounts.insert (d.address code) { accounts.findD (d.address code) default with code := runtimeBytecode },
          UInt256.ofNat (gas.toNat - 285800), substate, true, ByteArray.empty) := by
  have collision := deployment_collision_free d code fresh
  have codeFree := deployment_code_free d code fresh
  unfold Deployment.initialize Deployment.initialEnv Deployment.initialAccounts at initialized
  unfold Deployment.run
  rw [Lambda]
  unfold Deployment.address at collision codeFree initialized ⊢
  dsimp only at initialized codeFree
  simp only [collision, Bool.false_eq_true, if_false]
  erw [initialized]
  have first : runtimeBytecode[0]'(by rw [runtime_size]; decide) = 96 := by decide
  simp only [Bool.decide_or, decide_not, Fin.ofNat_eq_cast] at codeFree
  by_cases cost : gas.toNat < 285800
  · simp [runtime_size, first, GasConstants.Gcodedeposit, cost]
    rfl
  · simp [runtime_size, first, GasConstants.Gcodedeposit, cost]
    cases found : d.accounts.find? (d.address code) <;>
      simp only [Deployment.address, Fin.ofNat_eq_cast] at found <;>
      simp only [found] at codeFree ⊢ <;> simp_all

theorem deployment_outOfGas (d : Deployment) (code : ByteArray) (fresh : d.fresh code)
    (initialized : d.initialize code = .error .OutOfGass) :
    d.run code = (d.address code, d.created.insert (d.address code), d.accounts, ⟨0⟩,
      d.substate.addAccessedAccount (d.address code), false, ByteArray.empty) := by
  have collision := deployment_collision_free d code fresh
  unfold Deployment.initialize Deployment.initialEnv Deployment.initialAccounts at initialized
  unfold Deployment.run
  rw [Lambda]
  unfold Deployment.address at collision initialized ⊢
  dsimp only at initialized
  simp only [collision, Bool.false_eq_true, if_false]
  erw [initialized]

/-- A successful EVM deployment installs the pinned runtime at the returned address. -/
theorem deployment_success_code (d : Deployment) (sequencer : Address) (root : Root)
    (nonzero : sequencer ≠ 0)
    (fresh : d.fresh (creationBytecode ++ creationArgs (UInt256.ofNat sequencer.val) ⟨root⟩))
    (address : AccountAddress) (created : Batteries.RBSet AccountAddress compare)
    (accounts : AccountMap) (gas : UInt256) (substate : Substate) (data : ByteArray)
    (deployed : d.run (creationBytecode ++ creationArgs (UInt256.ofNat sequencer.val) ⟨root⟩) =
      (address, created, accounts, gas, substate, true, data)) :
    (accounts.find? address).map (·.code) = some runtimeBytecode := by
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
      dsimp only at addressEq accountsEq
      rw [addressEq, accountsEq]
      rw [accountMap_find_insert_self]
      rfl

end Rollup.EVM
