import proofs.CallbackStorage
import proofs.WorldPrecompiles

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Rollup.EVM

/-- A call into locked rollup code can keep only the incoming transfer. -/
theorem locked_own_call_accounts
    {blobs cA gh bl accounts original substate sender origin self gas price value contextValue
      calldata depth header writable cA' after gas' substate' accepted output}
    (pinned : (accounts.findD self default).code = runtimeBytecode)
    (locked : (accounts.findD self default).storage.findD ⟨6⟩ ⟨0⟩ ≠ ⟨0⟩)
    (run : Θ blobs cA gh bl accounts original substate sender origin self
      (toExecute accounts self) gas price value contextValue calldata depth header writable =
      (cA', after, gas', substate', accepted, output)) :
    after = accounts ∨ after = sendEth self sender value true accounts := by
  by_cases precompile : self ∈ π
  · have selected : toExecute accounts self = .Precompiled self := by simp [toExecute, precompile]
    rw [selected] at run
    exact precompiled_call_accounts run
  · let call : MessageCall := {
      blobs := blobs, created := cA, genesis := gh, blocks := bl, accounts := accounts,
      original := original, substate := substate, sender := sender, origin := origin,
      receiver := self, gas := gas, gasPrice := price, value := value,
      contextValue := contextValue, calldata := calldata, depth := depth,
      header := header, writable := writable }
    rw [pinned_toExecute precompile pinned] at run
    have locked' : solcSlotWord call.accounts (call.environment runtimeBytecode) ⟨6⟩ ≠ ⟨0⟩ := by
      rw [solc_slot_default]
      exact locked
    cases accepted with
    | false => exact .inl (message_call_rejected call runtimeBytecode cA' after gas' substate' output run).1
    | true => exact .inr (locked_message_call_accepted_any call cA' after gas' substate' output locked' run).2.2

/-- A funded call into the locked rollup preserves total ETH and cannot debit the rollup. -/
theorem locked_own_call_balances
    {blobs cA gh bl accounts original substate sender origin self gas price value contextValue
      calldata depth header writable cA' after gas' substate' accepted output}
    (pinned : (accounts.findD self default).code = runtimeBytecode)
    (locked : (accounts.findD self default).storage.findD ⟨6⟩ ⟨0⟩ ≠ ⟨0⟩)
    (funds : value.toNat ≤ ethLedger accounts sender)
    (world : worldEth accounts < wordLimit)
    (run : Θ blobs cA gh bl accounts original substate sender origin self
      (toExecute accounts self) gas price value contextValue calldata depth header writable =
      (cA', after, gas', substate', accepted, output)) :
    worldEth after = worldEth accounts ∧ ethLedger accounts self ≤ ethLedger after self := by
  rcases locked_own_call_accounts pinned locked run with rfl | rfl
  · exact ⟨rfl, Nat.le_refl _⟩
  · refine ⟨sendEth_world accounts self sender value true funds world, ?_⟩
    by_cases same : self = sender
    · subst sender
      rw [sendEth_self_ledger]
    · exact sendEth_other_balance accounts self sender self value true same funds world

end Rollup.EVM
