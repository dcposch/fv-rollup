import proofs.CallbackBalances

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- A locked rollup payment permits callback surplus but no additional debit. -/
theorem payment_call_balances
    {blobs cA gh bl accounts original substate self origin receiver gas price value contextValue
      calldata depth header writable cA' after gas' substate' output}
    (funds : value.toNat ≤ ethLedger accounts self)
    (initial : LockedWorld self accounts)
    (run : Θ blobs cA gh bl accounts original substate self origin receiver
      (toExecute accounts receiver) gas price value contextValue calldata depth header writable =
      (cA', after, gas', substate', true, output)) :
    worldEth after ≤ worldEth accounts ∧
      ethLedger accounts self - value.toNat ≤ ethLedger after self := by
  have pinned := LockedWorld.pinned initial
  have locked := LockedWorld.locked initial
  have world := LockedWorld.bounded initial
  by_cases own : receiver = self
  · subst receiver
    have balances := locked_own_call_balances pinned locked funds world run
    exact ⟨balances.1.le, (Nat.sub_le _ _).trans balances.2⟩
  have transferWorld := sendEth_world accounts receiver self value true funds world
  have transferBalance := sendEth_sender_lower_bound accounts receiver self value true funds world
  cases selected : toExecute accounts receiver with
  | Precompiled pc =>
    rw [selected] at run
    rcases precompiled_call_accounts run with same | same
    · rw [same]
      exact ⟨Nat.le_refl _, Nat.sub_le _ _⟩
    · rw [same]
      exact ⟨transferWorld.le, transferBalance⟩
  | Code bytes =>
    rw [selected] at run
    let call : MessageCall := {
      blobs := blobs, created := cA, genesis := gh, blocks := bl, accounts := accounts,
      original := original, substate := substate, sender := self, origin := origin,
      receiver := receiver, gas := gas, gasPrice := price, value := value,
      contextValue := contextValue, calldata := calldata, depth := depth,
      header := header, writable := writable }
    have execution := (message_call_accepted call bytes cA' after gas' substate' output run).1
    have storage : CodeStorageFrame self accounts call.initialAccounts :=
      sendEth_accountStaticStateEq receiver self value true accounts self
    have transferred : LockedWorld self call.initialAccounts := by
      refine ⟨storage.2.2.symm.trans pinned, ?_, ?_⟩
      · rw [← storage.1]
        exact locked
      · change worldEth (sendEth receiver self value true accounts) < wordLimit
        rw [transferWorld]
        exact world
    have balances := foreign_execution_balances (env := call.environment bytes) (run := execution)
      (Ne.symm own) transferred
    exact ⟨balances.1.trans transferWorld.le, transferBalance.trans balances.2⟩

end Rollup.EVM
