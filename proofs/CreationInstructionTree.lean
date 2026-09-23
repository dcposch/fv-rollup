import proofs.CreationTree
import proofs.CreationOpcodeCases
import proofs.ChildBoundary
import proofs.InstructionStep

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- Creation instructions compose nonce, endowment, initialization, and code installation. -/
theorem creation_instruction_tree_refines
    {before after : Ethereum.State} {jumps : Array UInt256}
    {op : Operation} {arg : Option (UInt256 × Nat)} {ret}
    {self : Address} {keys : AccessScope}
    (foreign : self ≠ before.executionEnv.codeOwner)
    (instruction : (decode before.executionEnv.code before.machineState.pc).getD (.STOP, none) = (op, arg))
    (kind : op = .CREATE ∨ op = .CREATE2)
    (ready : BoundaryReady self before.accountMap keys)
    (safe : Safe (boundaryModel self before.accountMap keys))
    (frames : ChildFramesRefine self keys jumps before)
    (run : Xstep jumps before = .ok (after, ret)) :
    BoundaryRefines self keys before.accountMap after.accountMap := by
  obtain ⟨checked, cost, stepped, precheck, opcode, accounts⟩ := instruction_account_step instruction run
  have unchanged := precheck_accounts precheck
  have environment := Z_executionEnv_eq precheck
  have checkedForeign : self ≠ checked.executionEnv.codeOwner := by simpa only [environment] using foreign
  have checkedReady : BoundaryReady self checked.accountMap keys := by rwa [unchanged]
  have checkedSafe : Safe (boundaryModel self checked.accountMap keys) := by rwa [unchanged]
  have effect : BoundaryRefines self keys checked.accountMap stepped.accountMap := by
    rcases creation_opcode_cases kind opcode with same | ⟨site, arguments, bounded, allowed, result⟩
    · rw [same]
      exact ⟨checkedReady, checkedSafe, .initial⟩
    · let parent := { checked with executionEnv.depth := before.executionEnv.depth }
      let call := site.call parent cost allowed
      have entered := ChildCreationEntry.entered instruction precheck arguments bounded allowed
      have nonceEffect := boundary_nonce_refines self checked.executionEnv.codeOwner checked.accountMap keys
        checkedReady checkedSafe
      have nonce := creation_site_nonce site parent cost allowed bounded
      have funds := creation_site_funded site parent cost allowed
      rcases executed : call.run with ⟨address, created, finalAccounts, gas, substate, accepted, output⟩
      have createdEffect : BoundaryRefines self keys call.accounts finalAccounts := by
        apply creation_execution_refines call executed nonceEffect.1 nonceEffect.2.1 checkedForeign nonce funds
        intro fresh
        have receiver := creation_fresh_foreign call (BoundaryReady.pinned nonceEffect.1) fresh
        have different := creation_fresh_not_sender call nonce fresh
        have transfer := boundary_creation_transfer_refines self call.sender call.address call.accounts call.value keys
          nonceEffect.1 nonceEffect.2.1 checkedForeign different funds
        exact frames _ (.inr entered) receiver transfer.1 transfer.2.1
      rw [result]
      change BoundaryRefines self keys checked.accountMap call.run.2.2.1
      rw [executed]
      exact boundary_refines_trans nonceEffect createdEffect
  simpa only [accounts, unchanged] using effect

end Rollup.EVM
