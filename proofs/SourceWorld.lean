import proofs.SourceRefinement
import proofs.ProjectionEquivalence

open Solm Ethereum Reasoning.Theory

namespace Rollup.EVM

/-- Storage-write sequences preserve the complete ETH ledger. -/
theorem store_keys_ethLedger (evm : Ethereum.State) (self : Address) (writes : List (StorageKey × UInt256)) :
    ethLedger (storeKeys evm self writes).accountMap = ethLedger evm.accountMap := by
  induction writes generalizing evm with
  | nil => rfl
  | cons write rest ih =>
    rw [storeKeys, ih, source_store_ethLedger]

/-- Equivalent account maps have equal total ETH. -/
theorem world_eth_equiv {left right : AccountMap} (maps : accountMapEquiv left right) :
    worldEth left = worldEth right := by
  have ledger : ethLedger left = ethLedger right := by
    funext owner
    rw [ethLedger_lookup, ethLedger_lookup]
    exact congrArg UInt256.toNat
      (account_balance_equiv (left := { (default : Ethereum.State) with accountMap := left })
        (right := { (default : Ethereum.State) with accountMap := right }) maps owner)
  simp only [worldEth, ledger]

/-- Accepted source calls cannot increase total ETH, including arbitrary withdrawal callbacks. -/
theorem source_world_nonincrease (evm out : Ethereum.State) (locals : Store) (frame : Frame)
    (call : Call) (values : Option (List Value)) (keys : AccessScope)
    (bound : CallBound evm locals call) (accesses : entryKeys call.entry ⊆ keys)
    (code : OwnCode evm) (world : WorldBounded evm)
    (ready : StorageReady evm evm.executionEnv.codeOwner keys)
    (run : ExecTransitionBody config contract evm locals (entryTransition call.entry).body
      (.returned frame out values)) :
    worldEth out.accountMap ≤ worldEth evm.accountMap := by
  rcases call with ⟨caller, value, entry⟩
  have args := bound.2.2.2.2
  cases entry with
  | deposit owner =>
    change some (depositLocals owner) = some locals at args
    cases Option.some.inj args
    have ownerKey : StorageKey.pending owner ∈ keys := accesses (by simp [entryKeys])
    have lockKey : StorageKey.fixed 6 ∈ keys := ready.1 (by simp [fixedKeys])
    have separate : keySlot (.pending owner) ≠ ⟨6⟩ := by
      intro same
      have impossible := ready.2.1 (.pending owner) ownerKey (.fixed 6) lockKey same
      cases impossible
    obtain ⟨_, output, _⟩ := deposit_success_checks evm out owner frame values separate run
    rw [output]
    simp only [depositState, worldEth, source_store_ethLedger, le_refl]
  | executeBatch batch =>
    change some (batchLocals batch) = some locals at args
    cases Option.some.inj args
    have output := (batch_source_exact evm out batch frame values keys run).1
    rw [output, batch_execution_writes]
    simp only [worldEth, store_keys_ethLedger, le_refl]
  | withdrawPendingBalance owner amount =>
    change some (withdrawalLocals owner amount) = some locals at args
    cases Option.some.inj args
    obtain ⟨_, _, after, data, payment, _, _, output⟩ :=
      withdrawal_source_exact evm out owner amount frame values run
    have initial : LockedWorld (withdrawalLockedState evm).executionEnv.codeOwner
        (withdrawalLockedState evm).accountMap := by
      simpa only [withdrawalLockedState, storageStore_executionEnv] using withdrawal_locked_world code world
    have balances := (source_payment_balances initial payment).1
    rw [output]
    simpa only [withdrawalFinalState, withdrawalDebitedState, withdrawalLockedState,
      worldEth, source_store_ethLedger] using balances
  | read getter =>
    have binding : entryArgumentStore (.read getter) = some (getterLocals getter) := by
      cases getter <;> rfl
    rw [binding] at args
    cases Option.some.inj args
    have zero := getter_source_nonpayable getter evm out (getterLocals getter) frame values run
    have result := (getter_source_exact evm getter zero).2 _ run
    cases result
    exact Nat.le_refl _

end Rollup.EVM
