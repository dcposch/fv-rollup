import proofs.ExecutionTree
import semantics.recording.ExecutionTreeComplete
import proofs.CreationPostcheck

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- Accepted creation commits code returned by its recorded initialization frame. -/
theorem creation_tree_accepted_state (call : CreationCall)
    {frameOutcome : Except ExecutionException (ExecutionResult Ethereum.State)}
    (tree : FrameRun (call.entryState.machineState.gasAvailable.toNat + 1)
      (D_J call.environment.code 0) call.entryState frameOutcome)
    {address created accounts gas substate output}
    (accepted : call.run = (address, created, accounts, gas, substate, true, output)) :
    ∃ state data, frameOutcome = .ok (.success state data) ∧
      accounts = state.accountMap.insert call.address
        { state.accountMap.findD call.address default with code := data } := by
  obtain ⟨initCreated, initAccounts, initGas, initSubstate, returned, executed⟩ :=
    creation_call_accepted call accepted
  have installed := creation_call_installed call executed accepted
  have actual := frame_run_sound tree
  change X (call.gas.toNat + 1) (D_J call.environment.code 0) call.entryState = frameOutcome at actual
  rw [creation_execute_entry, actual] at executed
  cases frameOutcome with
  | error error => simp [bind, Except.bind] at executed
  | ok result =>
    cases result with
    | revert gas data =>
      simp only [bind, Except.bind] at executed
      cases Except.ok.inj executed
    | success state data =>
      simp only [bind, Except.bind] at executed
      have same := ExecutionResult.success.inj (Except.ok.inj executed)
      have accountsEq := congrArg (fun result => result.2.1) same.1
      change state.accountMap = initAccounts at accountsEq
      rw [← accountsEq, ← same.2] at installed
      exact ⟨state, data, rfl, installed⟩

/-- Creation composes its endowment, initialization, and code installation, or restores its checkpoint. -/
theorem creation_tree_refines (call : CreationCall) {self : Address} {keys : AccessScope}
    {frameOutcome : Except ExecutionException (ExecutionResult Ethereum.State)}
    (tree : FrameRun (call.entryState.machineState.gasAvailable.toNat + 1)
      (D_J call.environment.code 0) call.entryState frameOutcome)
    {address created accounts gas substate accepted output}
    (executed : call.run = (address, created, accounts, gas, substate, accepted, output))
    (ready : BoundaryReady self call.accounts keys) (safe : Safe (boundaryModel self call.accounts keys))
    (foreign : self ≠ call.sender)
    (nonce : (call.accounts.findD call.sender default).nonce ≠ ⟨0⟩)
    (funds : call.value.toNat ≤ ethLedger call.accounts call.sender)
    (frame : call.collision = false → FrameResultRefines self keys call.initialAccounts frameOutcome) :
    BoundaryRefines self keys call.accounts accounts := by
  cases accepted with
  | false =>
    rw [creation_call_rejected call executed]
    exact ⟨ready, safe, .initial⟩
  | true =>
    have fresh := creation_accepted_fresh call executed
    obtain ⟨state, data, outcome, same⟩ := creation_tree_accepted_state call tree executed
    have effect := frame fresh
    rw [outcome] at effect
    change BoundaryRefines self keys call.initialAccounts state.accountMap at effect
    have transfer := boundary_creation_transfer_refines self call.sender call.address call.accounts call.value keys
      ready safe foreign (creation_fresh_not_sender call nonce fresh) funds
    change BoundaryRefines self keys call.accounts call.initialAccounts at transfer
    have installation := boundary_foreign_code_refines self call.address state.accountMap data keys
      (creation_fresh_foreign call (BoundaryReady.pinned ready) fresh) effect.1 effect.2.1
    rw [same]
    exact boundary_refines_trans (boundary_refines_trans transfer effect) installation

/-- The complete record connects initialization execution to the creation boundary. -/
theorem creation_execution_refines (call : CreationCall) {self : Address} {keys : AccessScope}
    {address created accounts gas substate accepted output}
    (executed : call.run = (address, created, accounts, gas, substate, accepted, output))
    (ready : BoundaryReady self call.accounts keys) (safe : Safe (boundaryModel self call.accounts keys))
    (foreign : self ≠ call.sender)
    (nonce : (call.accounts.findD call.sender default).nonce ≠ ⟨0⟩)
    (funds : call.value.toNat ≤ ethLedger call.accounts call.sender)
    (frame : call.collision = false → FrameResultRefines self keys call.initialAccounts
      (X (call.entryState.machineState.gasAvailable.toNat + 1) (D_J call.environment.code 0) call.entryState)) :
    BoundaryRefines self keys call.accounts accounts := by
  obtain ⟨tree⟩ := frame_run_complete (call.entryState.machineState.gasAvailable.toNat + 1)
    (D_J call.environment.code 0) call.entryState
  exact creation_tree_refines call tree executed ready safe foreign nonce funds frame

end Rollup.EVM
