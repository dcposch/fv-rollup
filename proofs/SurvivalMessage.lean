import proofs.SurvivalEntry
import proofs.MessageTree

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- A message's successful EVM result has the lifecycle state of its actual code frame. -/
theorem message_execution_survival_result (call : MessageCall) (code : ByteArray) {self : Address}
    (frame : FrameResultSurvives self
      (X ((call.codeEntry code).machineState.gasAvailable.toNat + 1) (D_J code 0) (call.codeEntry code)))
    {created accounts gas substate output}
    (executed : call.execute code = .ok (.success (created, accounts, gas, substate) output)) :
    AccountSurvives self accounts created substate := by
  rw [message_execute_entry] at executed
  cases actual : X (call.gas.toNat + 1) (D_J code 0) (call.codeEntry code) with
  | error error => simp only [actual, bind, Except.bind] at executed; contradiction
  | ok outcome =>
    cases outcome with
    | revert remaining data =>
      simp only [actual, bind, Except.bind] at executed
      cases Except.ok.inj executed
    | success state data =>
      simp only [actual, bind, Except.bind] at executed
      have same := (ExecutionResult.success.inj (Except.ok.inj executed)).1
      change X ((call.codeEntry code).machineState.gasAvailable.toNat + 1)
        (D_J code 0) (call.codeEntry code) = .ok (.success state data) at actual
      rw [actual] at frame
      have c := congrArg (fun result => result.1) same
      have a := congrArg (fun result => result.2.1) same
      have s := congrArg (fun result => result.2.2.2) same
      dsimp only at c a s
      rw [← c, ← a, ← s]
      exact frame

/-- Message success, revert, and exception all preserve an existing account's lifecycle conditions. -/
theorem message_execution_survives (call : MessageCall) (code : ByteArray) {self : Address}
    (initial : AccountSurvives self call.accounts call.created call.substate)
    (frame : FrameResultSurvives self
      (X ((call.codeEntry code).machineState.gasAvailable.toNat + 1) (D_J code 0) (call.codeEntry code)))
    {created accounts gas substate accepted output}
    (run : call.run code = (created, accounts, gas, substate, accepted, output)) :
    AccountSurvives self accounts created substate := by
  cases executed : call.execute code with
  | error error =>
    rw [message_call_error call code error executed] at run
    cases run
    exact initial
  | ok outcome =>
    cases outcome with
    | revert remaining data =>
      rw [message_call_revert call code remaining data executed] at run
      cases run
      exact initial
    | success result data =>
      rcases result with ⟨nextCreated, nextAccounts, remaining, nextSubstate⟩
      have after := message_execution_survival_result call code frame executed
      cases empty : nextAccounts == ∅ with
      | true =>
        rw [message_call_empty call code nextCreated nextAccounts remaining nextSubstate data executed empty] at run
        cases run
        exact ⟨(AccountSurvives.pinned initial), (AccountSurvives.notCreated after), (AccountSurvives.notDeleted initial)⟩
      | false =>
        rw [message_call_success call code nextCreated nextAccounts remaining nextSubstate data executed empty] at run
        cases run
        exact after

end Rollup.EVM
