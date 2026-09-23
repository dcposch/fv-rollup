import proofs.support.ExecutionBudget
import proofs.CallTree
import proofs.CreationTree

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- A message preserves the world budget through transfer, execution, and rollback. -/
theorem message_tree_budget (call : MessageCall) (code : ByteArray)
    {frameOutcome : Except ExecutionException (ExecutionResult Ethereum.State)}
    (tree : FrameRun ((call.codeEntry code).machineState.gasAvailable.toNat + 1)
      (D_J code 0) (call.codeEntry code) frameOutcome)
    {created accounts gas substate accepted output}
    (executed : call.run code = (created, accounts, gas, substate, accepted, output))
    (world : worldEth call.accounts < wordLimit)
    (funds : call.value.toNat ≤ ethLedger call.accounts call.sender)
    (frame : FrameResultBudget call.initialAccounts frameOutcome) :
    worldEth accounts ≤ worldEth call.accounts := by
  cases accepted with
  | false => rw [(message_call_rejected call code created accounts gas substate output executed).1]
  | true =>
    obtain ⟨state, data, outcome, same⟩ := message_tree_accepted_state call code tree executed
    rw [outcome] at frame
    change worldEth state.accountMap ≤ worldEth call.initialAccounts at frame
    have transfer : worldEth call.initialAccounts = worldEth call.accounts :=
      sendEth_world call.accounts call.receiver call.sender call.value true funds world
    rw [same]
    exact frame.trans transfer.le

/-- Bind the message budget to the actual code execution. -/
theorem message_execution_budget (call : MessageCall) (code : ByteArray)
    {created accounts gas substate accepted output}
    (executed : call.run code = (created, accounts, gas, substate, accepted, output))
    (world : worldEth call.accounts < wordLimit)
    (funds : call.value.toNat ≤ ethLedger call.accounts call.sender)
    (frame : FrameResultBudget call.initialAccounts
      (X ((call.codeEntry code).machineState.gasAvailable.toNat + 1) (D_J code 0) (call.codeEntry code))) :
    worldEth accounts ≤ worldEth call.accounts := by
  obtain ⟨tree⟩ := frame_run_complete ((call.codeEntry code).machineState.gasAvailable.toNat + 1)
    (D_J code 0) (call.codeEntry code)
  exact message_tree_budget call code tree executed world funds frame

/-- A creation budget includes endowment, code installation, and rollback. -/
theorem creation_tree_budget (call : CreationCall)
    {frameOutcome : Except ExecutionException (ExecutionResult Ethereum.State)}
    (tree : FrameRun (call.entryState.machineState.gasAvailable.toNat + 1)
      (D_J call.environment.code 0) call.entryState frameOutcome)
    {address created accounts gas substate accepted output}
    (executed : call.run = (address, created, accounts, gas, substate, accepted, output))
    (world : worldEth call.accounts < wordLimit)
    (nonce : (call.accounts.findD call.sender default).nonce ≠ ⟨0⟩)
    (funds : call.value.toNat ≤ ethLedger call.accounts call.sender)
    (frame : call.collision = false → FrameResultBudget call.initialAccounts frameOutcome) :
    worldEth accounts ≤ worldEth call.accounts := by
  cases accepted with
  | false => rw [creation_call_rejected call executed]
  | true =>
    have fresh := creation_accepted_fresh call executed
    obtain ⟨state, data, outcome, same⟩ := creation_tree_accepted_state call tree executed
    have budget := frame fresh
    rw [outcome] at budget
    change worldEth state.accountMap ≤ worldEth call.initialAccounts at budget
    have transfer : worldEth call.initialAccounts = worldEth call.accounts :=
      sendEthCreate_world_ne call.accounts call.address call.sender call.value true
        (creation_fresh_not_sender call nonce fresh) funds world
    rw [same]
    have installed := ethLedger_insert_same_balance state.accountMap call.address
      { state.accountMap.findD call.address default with code := data } rfl
    simp only [worldEth, installed]
    exact budget.trans transfer.le

/-- Bind the creation budget to the actual initialization execution. -/
theorem creation_execution_budget (call : CreationCall)
    {address created accounts gas substate accepted output}
    (executed : call.run = (address, created, accounts, gas, substate, accepted, output))
    (world : worldEth call.accounts < wordLimit)
    (nonce : (call.accounts.findD call.sender default).nonce ≠ ⟨0⟩)
    (funds : call.value.toNat ≤ ethLedger call.accounts call.sender)
    (frame : call.collision = false → FrameResultBudget call.initialAccounts
      (X (call.entryState.machineState.gasAvailable.toNat + 1) (D_J call.environment.code 0) call.entryState)) :
    worldEth accounts ≤ worldEth call.accounts := by
  obtain ⟨tree⟩ := frame_run_complete (call.entryState.machineState.gasAvailable.toNat + 1)
    (D_J call.environment.code 0) call.entryState
  exact creation_tree_budget call tree executed world nonce funds frame

/-- Call helpers preserve the budget through code, precompiles, and disabled guards. -/
theorem call_site_tree_budget (site : CallSite) (before after : Ethereum.State)
    {returned : UInt256} (world : worldEth before.accountMap < wordLimit)
    (source : AccountAddress.ofUInt256 site.source = before.executionEnv.codeOwner ∨ site.value = ⟨0⟩)
    (frames : ∀ code, site.enabled before →
      toExecute before.accountMap (AccountAddress.ofUInt256 site.target) = .Code code →
      FrameResultBudget (site.message before).initialAccounts
        (X (((site.message before).codeEntry code).machineState.gasAvailable.toNat + 1)
          (D_J code 0) ((site.message before).codeEntry code)))
    (run : site.run before = .ok (returned, after)) :
    worldEth after.accountMap ≤ worldEth before.accountMap := by
  by_cases enabled : site.enabled before
  · have funds := call_site_funded site before enabled source
    have accountsSame := call_site_outcome site before after returned enabled run
    rcases outcome : site.outcome before with ⟨created, accounts, gas, substate, accepted, output⟩
    rw [outcome] at accountsSame
    rw [accountsSame]
    cases selected : toExecute before.accountMap (AccountAddress.ofUInt256 site.target) with
    | Code code =>
      rw [call_site_code site before code selected] at outcome
      exact message_execution_budget (site.message before) code outcome world funds (frames code enabled selected)
    | Precompiled pc =>
      unfold CallSite.outcome at outcome
      rw [selected] at outcome
      exact (precompiled_call_world funds world outcome).le
  · rw [call_site_disabled_accounts site before after returned enabled run]

end Rollup.EVM
