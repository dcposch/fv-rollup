import proofs.CallInstructionBudget
import proofs.CreationInstructionBudget
import proofs.InstructionTree

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- Every foreign instruction preserves the world budget when its recorded children do. -/
theorem instruction_tree_budget {before after : Ethereum.State} {jumps : Array UInt256} {ret}
    {self : Address} {keys : AccessScope} (children : InstructionChildren jumps before)
    (ordinary : self ∉ π) (foreign : self ≠ before.executionEnv.codeOwner)
    (ready : BoundaryReady self before.accountMap keys)
    (safe : Safe (boundaryModel self before.accountMap keys))
    (covered : children.covered self keys) (budget : children.budget self keys)
    (run : Xstep jumps before = .ok (after, ret)) :
    worldEth after.accountMap ≤ worldEth before.accountMap := by
  rcases decoded : (decode before.executionEnv.code before.machineState.pc).getD (.STOP, none) with ⟨op, arg⟩
  by_cases internal : LocalOperation op
  · obtain ⟨checked, cost, stepped, precheck, opcode, accounts⟩ := instruction_account_step decoded run
    have unchanged := precheck_accounts precheck
    have ledger := local_step_ethLedger internal opcode
    simp only [accounts, worldEth, ledger, unchanged, le_refl]
  · have frames := recorded_child_frames_budget children budget
    rcases nonlocal_operation_cases internal with calls | creations | rfl
    · exact call_instruction_tree_budget children ordinary foreign decoded calls ready safe covered frames run
    · exact creation_instruction_tree_budget foreign decoded creations ready safe frames run
    · obtain ⟨checked, cost, stepped, precheck, opcode, accounts⟩ := instruction_account_step decoded run
      have unchanged := precheck_accounts precheck
      have environment := Z_executionEnv_eq precheck
      have checkedForeign : self ≠ checked.executionEnv.codeOwner := by
        simpa only [environment] using foreign
      have world : worldEth checked.accountMap < wordLimit := by
        rw [unchanged]
        exact BoundaryReady.world ready
      have balances := selfdestruct_step_balances
        (before := { checked with executionEnv.depth := before.executionEnv.depth })
        self checkedForeign world opcode
      simpa only [accounts, unchanged] using balances.1

end Rollup.EVM
