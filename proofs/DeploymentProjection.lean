import proofs.DeploymentInitial
import proofs.CodeInstallation
import proofs.WithdrawalProjection

open Ethereum Ethereum.EVM Reasoning.Theory

namespace Rollup.EVM

/-- Zero-endowment creation preserves every ETH balance. -/
theorem deployment_initial_ethLedger (d : Deployment) (code : ByteArray) :
    ethLedger (d.initialAccounts code) = ethLedger d.accounts := by
  unfold Deployment.initialAccounts
  cases found : d.accounts.find? d.sender with
  | none => rfl
  | some account =>
    have balance : (account.balance - (⟨0⟩ : UInt256)).toNat = ethLedger d.accounts d.sender := by
      rw [UInt256_subzero]
      simp [ethLedger, Batteries.RBMap.findD, found]
    have debited := ethLedger_insert_same_balance d.accounts d.sender
      { account with balance := account.balance - ⟨0⟩ } balance
    rw [ethLedger_insert_same_balance _ _ _ ?_, debited]
    dsimp only
    rw [u256_zero_add, debited]
    rfl

/-- Fresh constructor writes agree with the source constructor state. -/
theorem deployment_written_state (d : Deployment) (sequencer : Address) (root : Root)
    (fresh : d.fresh (creationBytecode ++ creationArgs (UInt256.ofNat sequencer.val) ⟨root⟩)) :
    let code := creationBytecode ++ creationArgs (UInt256.ofNat sequencer.val) ⟨root⟩
    d.writtenAccounts sequencer root =
      (constructorState (accountView (d.address code) (d.initialAccounts code)) sequencer root).accountMap := by
  let code := creationBytecode ++ creationArgs (UInt256.ofNat sequencer.val) ⟨root⟩
  have zero := deployment_initial_read d code fresh ⟨0⟩
  have canonical : (UInt256.ofNat sequencer.val).toNat < _root_.EVM.addressModulus := by
    rw [address_word_toNat]
    exact sequencer.isLt
  change ((d.initialAccounts code).find? (d.address code) |>.option ⟨0⟩
    (fun account => account.storage.findD ⟨0⟩ ⟨0⟩)) = ⟨0⟩ at zero
  change sstoreAccountMap (d.address code)
    (sstoreAccountMap (d.address code) (d.initialAccounts code) ⟨0⟩
      (packedAddress _ (UInt256.ofNat sequencer.val))) ⟨1⟩ ⟨root⟩ = _
  rw [zero, packedAddress_zero _ canonical]
  simp only [constructorState, storageStore_accountMap, accountView]
  rfl

/-- Constructor writes preserve all ETH balances. -/
theorem deployment_written_ethLedger (d : Deployment) (sequencer : Address) (root : Root)
    (fresh : d.fresh (creationBytecode ++ creationArgs (UInt256.ofNat sequencer.val) ⟨root⟩)) :
    ethLedger (d.writtenAccounts sequencer root) = ethLedger d.accounts := by
  rw [deployment_written_state d sequencer root fresh]
  simp only [constructorState, source_store_ethLedger, accountView, deployment_initial_ethLedger]

/-- Fresh constructor output projects to the initial model, including pre-funded ETH. -/
theorem deployment_written_projection (d : Deployment) (sequencer : Address) (root : Root)
    (fresh : d.fresh (creationBytecode ++ creationArgs (UInt256.ofNat sequencer.val) ⟨root⟩))
    (present : (d.accounts.find? d.sender).isSome) :
    let self := d.address (creationBytecode ++ creationArgs (UInt256.ofNat sequencer.val) ⟨root⟩)
    boundaryModel self (d.writtenAccounts sequencer root) fixedKeys =
      initial self sequencer root (ethLedger d.accounts self) := by
  let code := creationBytecode ++ creationArgs (UInt256.ofNat sequencer.val) ⟨root⟩
  let state := accountView (d.address code) (d.initialAccounts code)
  obtain ⟨account, found⟩ := Option.isSome_iff_exists.mp (deployment_initial_present d code present)
  have projected := constructor_projection state sequencer root found (deployment_initial_read d code fresh)
  rw [project_boundary, ← deployment_written_state d sequencer root fresh] at projected
  simpa only [project_ethLedger, state, accountView, deployment_initial_ethLedger] using projected

/-- Fresh constructor output has sparse storage and an unlocked payment guard. -/
theorem deployment_written_ready (d : Deployment) (sequencer : Address) (root : Root)
    (fresh : d.fresh (creationBytecode ++ creationArgs (UInt256.ofNat sequencer.val) ⟨root⟩))
    (present : (d.accounts.find? d.sender).isSome) :
    let self := d.address (creationBytecode ++ creationArgs (UInt256.ofNat sequencer.val) ⟨root⟩)
    StorageReady (accountView self (d.writtenAccounts sequencer root)) self fixedKeys ∧
      readWord (accountView self (d.writtenAccounts sequencer root)) self ⟨6⟩ = ⟨0⟩ := by
  let code := creationBytecode ++ creationArgs (UInt256.ofNat sequencer.val) ⟨root⟩
  let state := accountView (d.address code) (d.initialAccounts code)
  obtain ⟨account, found⟩ := Option.isSome_iff_exists.mp (deployment_initial_present d code present)
  have zero := deployment_initial_read d code fresh
  rw [deployment_written_state d sequencer root fresh]
  refine ⟨constructor_storage_ready state sequencer root found zero, ?_⟩
  change readWord (constructorState state sequencer root) state.executionEnv.codeOwner ⟨6⟩ = ⟨0⟩
  rw [constructor_storage state sequencer root found ⟨6⟩]
  simpa using zero ⟨6⟩

end Rollup.EVM
