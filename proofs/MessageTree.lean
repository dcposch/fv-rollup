import proofs.ExecutionTree
import proofs.CallEntry
import proofs.MessageCall
import proofs.BoundaryTransfer

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- An accepted message commits the accounts of its recorded successful code frame. -/
theorem message_tree_accepted_state (call : MessageCall) (code : ByteArray)
    {frameOutcome : Except ExecutionException (ExecutionResult Ethereum.State)}
    (tree : FrameRun ((call.codeEntry code).machineState.gasAvailable.toNat + 1)
      (D_J code 0) (call.codeEntry code) frameOutcome)
    {created accounts gas substate output}
    (accepted : call.run code = (created, accounts, gas, substate, true, output)) :
    ∃ state data, frameOutcome = .ok (.success state data) ∧ accounts = state.accountMap := by
  have executed := (message_call_accepted call code created accounts gas substate output accepted).1
  have actual := frame_run_sound tree
  change X (call.gas.toNat + 1) (D_J code 0) (call.codeEntry code) = frameOutcome at actual
  rw [message_execute_entry, actual] at executed
  cases frameOutcome with
  | error error => simp [bind, Except.bind] at executed
  | ok result =>
    cases result with
    | revert gas data =>
      simp only [bind, Except.bind] at executed
      cases Except.ok.inj executed
    | success state data =>
      simp only [bind, Except.bind] at executed
      have same := (ExecutionResult.success.inj (Except.ok.inj executed)).1
      exact ⟨state, data, rfl, (congrArg (fun result => result.2.1) same).symm⟩

/-- A message composes its funded transfer with its recorded code result, or restores its checkpoint. -/
theorem message_tree_refines (call : MessageCall) (code : ByteArray) {self : Address} {keys : AccessScope}
    {frameOutcome : Except ExecutionException (ExecutionResult Ethereum.State)}
    (tree : FrameRun ((call.codeEntry code).machineState.gasAvailable.toNat + 1)
      (D_J code 0) (call.codeEntry code) frameOutcome)
    {created accounts gas substate accepted output}
    (executed : call.run code = (created, accounts, gas, substate, accepted, output))
    (ready : BoundaryReady self call.accounts keys) (safe : Safe (boundaryModel self call.accounts keys))
    (senderSafe : self ≠ call.sender ∨ call.value = ⟨0⟩)
    (funds : call.value.toNat ≤ ethLedger call.accounts call.sender)
    (frame : FrameResultRefines self keys call.initialAccounts frameOutcome) :
    BoundaryRefines self keys call.accounts accounts := by
  cases accepted with
  | false =>
    have restored := (message_call_rejected call code created accounts gas substate output executed).1
    rw [restored]
    exact ⟨ready, safe, .initial⟩
  | true =>
    obtain ⟨state, data, outcome, same⟩ := message_tree_accepted_state call code tree executed
    rw [outcome] at frame
    change BoundaryRefines self keys call.initialAccounts state.accountMap at frame
    have transfer := boundary_transfer_refines self call.sender call.receiver call.accounts call.value keys
      ready safe senderSafe funds
    change BoundaryRefines self keys call.accounts call.initialAccounts at transfer
    rw [same]
    exact boundary_refines_trans transfer frame

end Rollup.EVM
