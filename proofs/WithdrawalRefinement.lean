import semantics.SourceResult
import proofs.WithdrawalCallbackModel

open Solm Ethereum Reasoning.Theory

namespace Rollup.EVM

/-- An accepted source withdrawal has the exact model effect and actual payment. -/
theorem withdrawal_source_refines (evm out : Ethereum.State) (locals : Store) (frame : Frame)
    (caller owner : Address) (value amount : Nat) (values : Option (List Value)) (keys : AccessScope)
    (bound : CallBound evm locals ⟨caller, value, .withdrawPendingBalance owner amount⟩)
    (accesses : entryKeys (.withdrawPendingBalance owner amount) ⊆ keys)
    (code : OwnCode evm) (world : WorldBounded evm)
    (ready : StorageReady evm evm.executionEnv.codeOwner keys)
    (safe : Safe (beforeCall evm keys))
    (run : ExecTransitionBody config contract evm locals
      (entryTransition (.withdrawPendingBalance owner amount)).body (.returned frame out values)) :
    SourceResult evm out locals frame ⟨caller, value, .withdrawPendingBalance owner amount⟩ values keys := by
  have payment := source_payment_bound evm out locals frame
    ⟨caller, value, .withdrawPendingBalance owner amount⟩ values bound run
  have args := bound.2.2.2.2
  change some (withdrawalLocals owner amount) = some locals at args
  have sameLocals := Option.some.inj args
  subst locals
  have tracked : StorageKey.claims owner ∈ keys := accesses (by simp [entryKeys])
  obtain ⟨returned, checks, after, output, call, environment, frameEq, outputEq⟩ :=
    withdrawal_source_exact evm out owner amount frame values run
  have before : beforeCall evm keys = project evm evm.executionEnv.codeOwner keys := by
    simp [beforeCall, checks.nonpayable]
  have valueZero : value = 0 := by
    have valueEq := bound.2.1
    change value = evm.executionEnv.weiValue.toNat at valueEq
    simpa [checks.nonpayable, UInt256.toNat] using valueEq
  have credit := withdrawal_credit_model evm owner keys code ready tracked
  have covered : amount ≤ (project evm evm.executionEnv.codeOwner keys).claims owner := by
    simpa only [credit] using checks.covered
  have amountBound : amount < wordLimit := lt_of_le_of_lt checks.covered
    (readWord (withdrawalLockedState evm) evm.executionEnv.codeOwner (keySlot (.claims owner))).val.isLt
  have enabled : WithdrawalEnabled (project evm evm.executionEnv.codeOwner keys) owner amount := by
    refine ⟨rfl, Nat.pos_of_ne_zero checks.positive, covered, ?_⟩
    have totalBound := balance_le_total (project evm evm.executionEnv.codeOwner keys).claims owner
    have solvent := safe.1
    rw [before] at solvent
    have idle : (project evm evm.executionEnv.codeOwner keys).payment = none := rfl
    simp only [Solvent, liabilities, reserved, idle, Option.map_none, Option.getD_none,
      Nat.add_zero] at solvent
    change amount ≤ (project evm evm.executionEnv.codeOwner keys).eth
    omega
  have callback := withdrawal_callback_model keys code world amountBound call
  have storage := withdrawal_final_storage_ready keys code ready tracked call
  have balances := withdrawal_payment_balances code world amountBound call
  subst value
  subst values
  subst out
  refine ⟨storage.1, ?_, ?_, storage.2, ?_, .unit, [⟨owner, amount⟩], rfl, ?_, payment⟩
  · have lock := withdrawal_final_storage_values keys code ready tracked checks.unlocked call
      (.fixed 6) (ready.1 (by simp [fixedKeys]))
    simpa using lock.trans checks.unlocked
  · rw [withdrawal_final_writes evm after owner amount environment, storeKeys_environment, environment]
  · rw [withdrawal_final_writes evm after owner amount environment]
    exact storeKeys_worldBounded after _ _ balances.1
  · rw [before, withdrawal_final_projection keys code ready tracked checks.unlocked call]
    simpa only [finishWithdrawal, beginWithdrawal] using
      (CallStep.withdrawal (caller := caller) enabled callback)

end Rollup.EVM
