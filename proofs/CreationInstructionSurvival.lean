import proofs.CreationLifecycleCases
import proofs.SurvivalCreation
import proofs.ChildSurvival
import proofs.SurvivalLocal

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- Creation instructions preserve account survival through initialization and code installation. -/
theorem creation_instruction_survives
    {before after : Ethereum.State} {jumps : Array UInt256}
    {op : Operation} {arg : Option (UInt256 × Nat)} {ret} {self : Address}
    (initial : StateSurvives self before)
    (instruction : (decode before.executionEnv.code before.machineState.pc).getD (.STOP, none) = (op, arg))
    (kind : op = .CREATE ∨ op = .CREATE2)
    (frames : ChildFramesSurvive self jumps before)
    (run : Xstep jumps before = .ok (after, ret)) : StateSurvives self after := by
  obtain ⟨checked, cost, stepped, precheck, opcode, same⟩ := instruction_state_step instruction run
  have checkedSurvives := precheck_survives initial precheck
  have effect : StateSurvives self stepped := by
    rcases creation_opcode_lifecycle_cases kind opcode with unchanged |
      ⟨site, arguments, bounded, allowed, accounts, created, substate⟩
    · change AccountSurvives self stepped.accountMap stepped.createdAccounts stepped.substate
      rw [unchanged.1, unchanged.2.1, unchanged.2.2]
      exact checkedSurvives
    · let parent := { checked with executionEnv.depth := before.executionEnv.depth }
      let call := site.call parent cost allowed
      have callInitial : AccountSurvives self call.accounts call.created call.substate :=
        nonce_survives checkedSurvives
      have entered := ChildCreationEntry.entered instruction precheck arguments bounded allowed
      have child := frames _ (.inr entered) (creation_entry_survives call callInitial)
      have result := creation_execution_survives call callInitial child (rfl : call.run = call.run)
      change AccountSurvives self stepped.accountMap stepped.createdAccounts stepped.substate
      rw [accounts, created, substate]
      exact result
  rw [same]
  exact effect

end Rollup.EVM
