import proofs.Boundary
import proofs.WorldTransfers

open Ethereum Ethereum.EVM Solm Reasoning.Theory

namespace Rollup.EVM

theorem message_initial_accounts (call : MessageCall) :
    call.initialAccounts = sendEth call.receiver call.sender call.value true call.accounts := rfl

/-- A funded incoming transfer increases the receiver balance by exactly its value. -/
theorem message_initial_balance (call : MessageCall)
    (different : call.receiver ≠ call.sender)
    (funds : call.value.toNat ≤ ethLedger call.accounts call.sender)
    (world : worldEth call.accounts < wordLimit) :
    ethLedger call.initialAccounts call.receiver =
      ethLedger call.accounts call.receiver + call.value.toNat := by
  rw [message_initial_accounts, sendEth_ledger_ne _ _ _ _ different funds world]
  simp [debit, credit, Function.update]
  intro same
  exact False.elim (different same)

/-- The incoming transfer changes only ETH in the rollup projection. -/
theorem message_initial_projection (call : MessageCall) (keys : AccessScope)
    (different : call.receiver ≠ call.sender)
    (funds : call.value.toNat ≤ ethLedger call.accounts call.sender)
    (world : worldEth call.accounts < wordLimit) :
    boundaryModel call.receiver call.initialAccounts keys =
      { boundaryModel call.receiver call.accounts keys with
        eth := (boundaryModel call.receiver call.accounts keys).eth + call.value.toNat } := by
  have frame : CodeStorageFrame call.receiver call.accounts call.initialAccounts :=
    sendEth_accountStaticStateEq call.receiver call.sender call.value true call.accounts call.receiver
  have projected := CodeStorageFrame.project
    (before := accountView call.receiver call.accounts)
    (after := accountView call.receiver call.initialAccounts) frame keys
  have balance : (boundaryModel call.receiver call.initialAccounts keys).eth =
      (boundaryModel call.receiver call.accounts keys).eth + call.value.toNat := by
    simp only [boundaryModel, project_ethLedger, accountView]
    exact message_initial_balance call different funds world
  change boundaryModel call.receiver call.initialAccounts keys =
    { boundaryModel call.receiver call.accounts keys with
      eth := (boundaryModel call.receiver call.initialAccounts keys).eth } at projected
  rwa [balance] at projected

/-- Subtract incoming value once to recover the state before the message call. -/
theorem message_before_model (call : MessageCall) (keys : AccessScope)
    (different : call.receiver ≠ call.sender)
    (ordinary : call.contextValue = call.value)
    (funds : call.value.toNat ≤ ethLedger call.accounts call.sender)
    (world : worldEth call.accounts < wordLimit) :
    beforeCall call.entryState keys = boundaryModel call.receiver call.accounts keys := by
  simp only [beforeCall, project_boundary, MessageCall.entryState, MessageCall.environment]
  rw [message_initial_projection call keys different funds world, ordinary]
  simp

/-- Incoming ETH preserves the conditions needed by the runtime proof. -/
theorem message_entry_ready (call : MessageCall) (keys : AccessScope)
    (ready : BoundaryReady call.receiver call.accounts keys)
    (different : call.receiver ≠ call.sender)
    (ordinary : call.contextValue = call.value)
    (funds : call.value.toNat ≤ ethLedger call.accounts call.sender) :
    OwnCode call.entryState ∧ WorldBounded call.entryState ∧
      StorageReady call.entryState call.receiver keys ∧
      readWord call.entryState call.receiver ⟨6⟩ = ⟨0⟩ ∧
      call.entryState.executionEnv.weiValue.toNat ≤ (project call.entryState call.receiver keys).eth := by
  have frame : CodeStorageFrame call.receiver call.accounts call.initialAccounts :=
    sendEth_accountStaticStateEq call.receiver call.sender call.value true call.accounts call.receiver
  have pinned := frame.2.2.symm.trans (BoundaryReady.pinned ready)
  obtain ⟨account, found, code⟩ := pinned_account_present pinned
  refine ⟨⟨rfl, ?_⟩, ?_, ?_, ?_, ?_⟩
  · change (call.initialAccounts.find? call.receiver).map (·.code) = some runtimeBytecode
    simp only [found, Option.map_some, code]
  · apply (worldBounded_iff_worldEth call.entryState).mpr
    change worldEth call.initialAccounts < wordLimit
    rw [message_initial_accounts, sendEth_world _ _ _ _ _ funds (BoundaryReady.world ready)]
    exact BoundaryReady.world ready
  · exact CodeStorageFrame.storageReady (before := accountView call.receiver call.accounts)
      (after := call.entryState) frame ready.2.2.1
  · rw [readWord_default]
    change (call.initialAccounts.findD call.receiver default).storage.findD ⟨6⟩ ⟨0⟩ = ⟨0⟩
    rw [← frame.1]
    simpa only [readWord_default, accountView] using ready.2.2.2
  · rw [project_ethLedger]
    change call.contextValue.toNat ≤ ethLedger call.initialAccounts call.receiver
    rw [ordinary, message_initial_balance call different funds (BoundaryReady.world ready)]
    omega

end Rollup.EVM
