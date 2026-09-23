import proofs.ExecutionBudgetWrappers
import proofs.CreationOpcodeCases
import proofs.ChildBudget
import proofs.InstructionStep

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- Creation instructions preserve the ETH budget across all creation stages. -/
theorem creation_instruction_tree_budget
    {before after : Ethereum.State} {jumps : Array UInt256}
    {op : Operation} {arg : Option (UInt256 × Nat)} {ret}
    {self : Address} {keys : AccessScope}
    (foreign : self ≠ before.executionEnv.codeOwner)
    (instruction : (decode before.executionEnv.code before.machineState.pc).getD (.STOP, none) = (op, arg))
    (kind : op = .CREATE ∨ op = .CREATE2)
    (ready : BoundaryReady self before.accountMap keys)
    (safe : Safe (boundaryModel self before.accountMap keys))
    (frames : ChildFramesBudget self keys jumps before)
    (run : Xstep jumps before = .ok (after, ret)) :
    worldEth after.accountMap ≤ worldEth before.accountMap := by
  obtain ⟨checked, cost, stepped, precheck, opcode, accounts⟩ := instruction_account_step instruction run
  have unchanged := precheck_accounts precheck
  have environment := Z_executionEnv_eq precheck
  have checkedForeign : self ≠ checked.executionEnv.codeOwner := by simpa only [environment] using foreign
  have checkedReady : BoundaryReady self checked.accountMap keys := by rwa [unchanged]
  have checkedSafe : Safe (boundaryModel self checked.accountMap keys) := by rwa [unchanged]
  have effect : worldEth stepped.accountMap ≤ worldEth checked.accountMap := by
    rcases creation_opcode_cases kind opcode with same | ⟨site, arguments, bounded, allowed, result⟩
    · rw [same]
    · let parent := { checked with executionEnv.depth := before.executionEnv.depth }
      let call := site.call parent cost allowed
      have entered := ChildCreationEntry.entered instruction precheck arguments bounded allowed
      have nonceEffect := boundary_nonce_refines self checked.executionEnv.codeOwner checked.accountMap keys
        checkedReady checkedSafe
      have nonce := creation_site_nonce site parent cost allowed bounded
      have funds := creation_site_funded site parent cost allowed
      rcases executed : call.run with ⟨address, created, finalAccounts, gas, substate, accepted, output⟩
      have createdEffect : worldEth finalAccounts ≤ worldEth call.accounts := by
        apply creation_execution_budget call executed (BoundaryReady.world nonceEffect.1) nonce funds
        intro fresh
        have receiver := creation_fresh_foreign call (BoundaryReady.pinned nonceEffect.1) fresh
        have different := creation_fresh_not_sender call nonce fresh
        have transfer := boundary_creation_transfer_refines self call.sender call.address call.accounts call.value keys
          nonceEffect.1 nonceEffect.2.1 checkedForeign different funds
        exact frames _ (.inr entered) receiver transfer.1 transfer.2.1
      rw [result]
      change worldEth call.run.2.2.1 ≤ worldEth checked.accountMap
      rw [executed]
      have total : worldEth call.accounts = worldEth checked.accountMap := by
        change worldEth (incrementNonce checked.accountMap checked.executionEnv.codeOwner) = _
        simp only [worldEth, incrementNonce_ethLedger]
      exact createdEffect.trans total.le
  simpa only [accounts, unchanged] using effect

end Rollup.EVM
