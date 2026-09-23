import proofs.SurvivalEntry
import proofs.CreationPostcheck

open Ethereum Ethereum.EVM Reasoning.Theory

namespace Rollup.EVM

/-- A successful initialization result has the lifecycle state of its actual code frame. -/
theorem creation_execution_survival_result (call : CreationCall) {self : Address}
    (frame : FrameResultSurvives self
      (X (call.entryState.machineState.gasAvailable.toNat + 1) (D_J call.environment.code 0) call.entryState))
    {created accounts gas substate output}
    (executed : call.execute = .ok (.success (created, accounts, gas, substate) output)) :
    AccountSurvives self accounts created substate := by
  rw [creation_execute_entry] at executed
  cases actual : X (call.gas.toNat + 1) (D_J call.environment.code 0) call.entryState with
  | error error => simp only [actual, bind, Except.bind] at executed; contradiction
  | ok outcome =>
    cases outcome with
    | revert remaining data =>
      simp only [actual, bind, Except.bind] at executed
      cases Except.ok.inj executed
    | success state data =>
      simp only [actual, bind, Except.bind] at executed
      have same := (ExecutionResult.success.inj (Except.ok.inj executed)).1
      change X (call.entryState.machineState.gasAvailable.toNat + 1)
        (D_J call.environment.code 0) call.entryState = .ok (.success state data) at actual
      rw [actual] at frame
      have c := congrArg (fun result => result.1) same
      have a := congrArg (fun result => result.2.1) same
      have s := congrArg (fun result => result.2.2.2) same
      dsimp only at c a s
      rw [← c, ← a, ← s]
      exact frame

/-- Creation postchecks retain the returned creation set and select the correct substate. -/
theorem creation_success_lifecycle (call : CreationCall)
    {address created accounts gas substate accepted output initCreated initAccounts initGas initSubstate returned}
    (execution : call.execute = .ok (.success (initCreated, initAccounts, initGas, initSubstate) returned))
    (run : call.run = (address, created, accounts, gas, substate, accepted, output)) :
    created = initCreated ∧ (substate = call.substate.addAccessedAccount call.address ∨ substate = initSubstate) := by
  unfold CreationCall.execute CreationCall.initialCreated CreationCall.initialAccounts
    CreationCall.environment CreationCall.collision CreationCall.address Deployment.address at execution
  unfold CreationCall.run Lambda at run
  dsimp only at execution run
  simp only [apply_ite] at execution run
  erw [execution] at run
  have createdEq := congrArg (fun result => result.2.1) run
  have substateEq := congrArg (fun result => result.2.2.2.2.1) run
  dsimp only at createdEq substateEq
  refine ⟨createdEq.symm, ?_⟩
  split_ifs at substateEq
  · exact .inl substateEq.symm
  · exact .inr substateEq.symm

/-- Creation, including failed code postchecks, preserves every pre-existing pinned rollup. -/
theorem creation_execution_survives (call : CreationCall) {self : Address}
    (initial : AccountSurvives self call.accounts call.created call.substate)
    (frame : FrameResultSurvives self
      (X (call.entryState.machineState.gasAvailable.toNat + 1) (D_J call.environment.code 0) call.entryState))
    {address created accounts gas substate accepted output}
    (run : call.run = (address, created, accounts, gas, substate, accepted, output)) :
    AccountSurvives self accounts created substate := by
  have startingCreated := creation_initial_set_excludes call
    (AccountSurvives.pinned initial) (AccountSurvives.notCreated initial)
  have startingDeleted : self ∉ (call.substate.addAccessedAccount call.address).selfDestructSet :=
    show self ∉ call.substate.selfDestructSet from AccountSurvives.notDeleted initial
  cases executed : call.execute with
  | error error =>
    rw [creation_call_error call error executed] at run
    cases run
    exact ⟨AccountSurvives.pinned initial, startingCreated, startingDeleted⟩
  | ok outcome =>
    cases outcome with
    | revert remaining data =>
      rw [creation_call_revert call remaining data executed] at run
      cases run
      exact ⟨AccountSurvives.pinned initial, startingCreated, startingDeleted⟩
    | success result data =>
      rcases result with ⟨nextCreated, nextAccounts, remaining, nextSubstate⟩
      have survived := creation_execution_survival_result call frame executed
      have metadata := creation_success_lifecycle call executed run
      have notCreated : self ∉ created := by
        rw [metadata.1]
        exact AccountSurvives.notCreated survived
      have notDeleted : self ∉ substate.selfDestructSet := by
        rcases metadata.2 with reverted | kept
        · rw [reverted]
          exact startingDeleted
        · rw [kept]
          exact AccountSurvives.notDeleted survived
      refine ⟨?_, notCreated, notDeleted⟩
      cases accepted with
      | false =>
        rw [creation_call_rejected call run]
        exact AccountSurvives.pinned initial
      | true =>
        have different := creation_fresh_foreign call (AccountSurvives.pinned initial)
          (creation_accepted_fresh call run)
        rw [creation_call_installed call executed run]
        simp only [Batteries.RBMap.findD, accountMap_find?_insert_ne _ _ _ _ different]
        exact AccountSurvives.pinned survived

end Rollup.EVM
