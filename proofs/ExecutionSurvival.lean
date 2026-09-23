import proofs.TreeSurvival
import proofs.RecordedExecution
import proofs.SurvivalPrecompile
import proofs.SurroundingMessage

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- Actual EVM execution preserves account survival without a child-correctness premise. -/
theorem execution_survives (fuel : Nat) (jumps : Array UInt256) (start : Ethereum.State)
    {self : Address} (initial : StateSurvives self start) :
    FrameResultSurvives self (X fuel jumps start) :=
  frame_run_survives (executionRecord fuel jumps start) self initial

/-- A code message preserves existing account code and excludes it from both lifecycle sets. -/
theorem message_survives (call : MessageCall) (code : ByteArray) {self : Address}
    {created accounts gas substate accepted output}
    (initial : AccountSurvives self call.accounts call.created call.substate)
    (executed : call.run code = (created, accounts, gas, substate, accepted, output)) :
    AccountSurvives self accounts created substate :=
  message_execution_survives call code initial
    (execution_survives _ _ _ (message_entry_survives call code initial)) executed

/-- The actual selected message preserves account survival through code or a precompile. -/
theorem selected_message_survives (call : MessageCall) {self : Address}
    {created accounts gas substate accepted output}
    (initial : AccountSurvives self call.accounts call.created call.substate)
    (executed : call.selectedRun = (created, accounts, gas, substate, accepted, output)) :
    AccountSurvives self accounts created substate := by
  unfold MessageCall.selectedRun at executed
  cases selected : toExecute call.accounts call.receiver with
  | Code code =>
    rw [selected] at executed
    exact message_survives call code initial executed
  | Precompiled pc =>
    rw [selected] at executed
    exact precompiled_call_survives initial executed

/-- The actual creation result preserves survival through all nested execution. -/
theorem creation_survives (call : CreationCall) {self : Address}
    {address created accounts gas substate accepted output}
    (initial : AccountSurvives self call.accounts call.created call.substate)
    (executed : call.run = (address, created, accounts, gas, substate, accepted, output)) :
    AccountSurvives self accounts created substate :=
  creation_execution_survives call initial
    (execution_survives _ _ _ (creation_entry_survives call initial)) executed

end Rollup.EVM
