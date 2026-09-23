import proofs.ExecutionBudgetWrappers
import proofs.RollupCallBudget
import proofs.ChildBudget
import proofs.ChildTreeCoverage
import proofs.RollupCallInstruction

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- Call instructions preserve the budget through their actual child or rollup entry. -/
theorem call_instruction_tree_budget
    {before after : Ethereum.State} {jumps : Array UInt256}
    {op : Operation} {arg : Option (UInt256 × Nat)} {ret}
    {self : Address} {keys : AccessScope}
    (children : InstructionChildren jumps before)
    (ordinary : self ∉ π) (foreign : self ≠ before.executionEnv.codeOwner)
    (instruction : (decode before.executionEnv.code before.machineState.pc).getD (.STOP, none) = (op, arg))
    (kind : op = .CALL ∨ op = .CALLCODE ∨ op = .DELEGATECALL ∨ op = .STATICCALL)
    (ready : BoundaryReady self before.accountMap keys)
    (safe : Safe (boundaryModel self before.accountMap keys))
    (covered : children.covered self keys)
    (frames : ChildFramesBudget self keys jumps before)
    (run : Xstep jumps before = .ok (after, ret)) :
    worldEth after.accountMap ≤ worldEth before.accountMap := by
  obtain ⟨checked, cost, stepped, precheck, opcode, accounts⟩ := instruction_account_step instruction run
  obtain ⟨site, arguments, returned, during, helper, helperAccounts⟩ := call_opcode_helper kind opcode
  have unchanged := precheck_accounts precheck
  have environment := Z_executionEnv_eq precheck
  have checkedForeign : self ≠ checked.executionEnv.codeOwner := by simpa only [environment] using foreign
  have checkedReady : BoundaryReady self checked.accountMap keys := by rwa [unchanged]
  have checkedSafe : Safe (boundaryModel self checked.accountMap keys) := by rwa [unchanged]
  let parent := callParent { checked with executionEnv.depth := before.executionEnv.depth }
  have source := call_opcode_source arguments
  have senderSafe : self ≠ (site.message parent).sender ∨ site.value = ⟨0⟩ := by
    rcases source with source | zero
    · exact .inl (by simpa only [CallSite.message, source] using checkedForeign)
    · exact .inr zero
  have effect : worldEth during.accountMap ≤ worldEth checked.accountMap := by
    by_cases enabled : site.enabled parent
    · by_cases receiver : AccountAddress.ofUInt256 site.recipient = self
      · have target := call_opcode_target checkedForeign arguments receiver
        have selected : toExecute checked.accountMap (AccountAddress.ofUInt256 site.target) = .Code runtimeBytecode := by
          rw [target]
          exact pinned_toExecute ordinary (BoundaryReady.pinned checkedReady)
        have entered := ChildCallEntry.entered instruction precheck arguments enabled selected
        have access := child_call_calldata_covered children covered entered receiver
        exact call_helper_rollup_budget
          (before := { checked with executionEnv.depth := before.executionEnv.depth })
          ordinary checkedForeign arguments receiver enabled
          checkedReady access helper
      · apply call_site_tree_budget site parent during (BoundaryReady.world checkedReady) source
          (run := helper)
        intro code enabled selected
        have entered := ChildCallEntry.entered instruction precheck arguments enabled selected
        have funds := call_site_funded site parent enabled source
        have transfer := boundary_transfer_refines self (site.message parent).sender
          (site.message parent).receiver checked.accountMap site.value keys
          checkedReady checkedSafe senderSafe funds
        exact frames _ (.inl entered) (Ne.symm receiver) transfer.1 transfer.2.1
    · rw [call_site_disabled_accounts site parent during returned enabled helper]
      exact Nat.le_refl _
  simpa only [accounts, helperAccounts, unchanged] using effect

end Rollup.EVM
