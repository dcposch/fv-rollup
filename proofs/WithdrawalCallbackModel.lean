import proofs.WithdrawalProjection

open Ethereum

namespace Rollup

/-- A balance increase with fixed state is an allowed callback donation. -/
theorem callback_of_surplus (state : State) (balance : Nat)
    (lower : state.eth ≤ balance) (bounded : balance < wordLimit) :
    Callback state { state with eth := balance } := by
  have amount : state.eth + (balance - state.eth) = balance := Nat.add_sub_of_le lower
  have callback := Callback.donation (Callback.refl state) (balance - state.eth) (by omega)
  simpa only [donate, amount] using callback

namespace EVM

/-- The proved payment bounds give the model callback relation. -/
theorem withdrawal_callback_model {before after : Ethereum.State} {owner : Address}
    {amount : Nat} {output : ByteArray} (keys : AccessScope)
    (code : OwnCode before) (world : WorldBounded before)
    (amountBound : amount < wordLimit)
    (call : Solm.callViaEVM (withdrawalLockedState before) owner amount ByteArray.empty
      (true, after, output)) :
    Callback (beginWithdrawal (project before before.executionEnv.codeOwner keys) owner amount)
      { beginWithdrawal (project before before.executionEnv.codeOwner keys) owner amount with
        eth := (project after before.executionEnv.codeOwner keys).eth } := by
  have balances := withdrawal_payment_balances code world amountBound call
  have lower : (project before before.executionEnv.codeOwner keys).eth - amount ≤
      (project after before.executionEnv.codeOwner keys).eth := by
    simp only [project_ethLedger]
    simpa only [withdrawalLockedState, source_store_ethLedger] using balances.2
  apply callback_of_surplus _ _ lower
  rw [project_ethLedger]
  exact (after.accountMap.findD before.executionEnv.codeOwner default).balance.val.isLt

end EVM
end Rollup
