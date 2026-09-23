import proofs.CallLifecycle
import proofs.ChildSurvival
import proofs.SurvivalLocal

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- Call instructions preserve account survival through their actual selected child. -/
theorem call_instruction_survives
    {before after : Ethereum.State} {jumps : Array UInt256}
    {op : Operation} {arg : Option (UInt256 × Nat)} {ret} {self : Address}
    (initial : StateSurvives self before)
    (instruction : (decode before.executionEnv.code before.machineState.pc).getD (.STOP, none) = (op, arg))
    (kind : op = .CALL ∨ op = .CALLCODE ∨ op = .DELEGATECALL ∨ op = .STATICCALL)
    (frames : ChildFramesSurvive self jumps before)
    (run : Xstep jumps before = .ok (after, ret)) : StateSurvives self after := by
  obtain ⟨checked, cost, stepped, precheck, opcode, same⟩ := instruction_state_step instruction run
  obtain ⟨site, arguments, returned, during, helper, accounts, created, substate⟩ :=
    call_opcode_lifecycle kind opcode
  have checkedSurvives := precheck_survives initial precheck
  let parent := callParent { checked with executionEnv.depth := before.executionEnv.depth }
  have effect : StateSurvives self during := by
    apply call_site_survives site parent during checkedSurvives (run := helper)
    intro code enabled selected
    have entered := ChildCallEntry.entered instruction precheck arguments enabled selected
    exact frames _ (.inl entered)
      (message_entry_survives (site.message parent) code
        (call_site_initial_survives site parent checkedSurvives))
  rw [same]
  change AccountSurvives self stepped.accountMap stepped.createdAccounts stepped.substate
  rw [accounts, created, substate]
  exact effect

end Rollup.EVM
