import proofs.WithdrawalBytecodeExecution
import Reasoning.Dispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Rollup.EVM

/-- Passed prelude checks give equivalent source and bytecode outcomes for any receiver. -/
theorem withdrawal_checked_equivalence {cA gh bl σ σ_solm σ₀ A I} {g : UInt256}
    (code : I.code = runtimeBytecode) (writable : I.perm = true)
    (bounded : I.calldata.size < UInt256.size)
    (selector : solcSelectorWord I = ⟨0xbb3ef682⟩) (maps : accountMapEquiv σ σ_solm)
    (checks : WithdrawalBytecodeChecks σ I) :
    runtimeEquivalenceFor config contract cA gh bl σ σ_solm σ₀ g A I := by
  let initial := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
  let sourceInitial := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let owner := withdrawalOwnerFromCalldata I
  let amount := (calldataWord I.calldata 36).toNat
  have ownerBinding : UInt256.ofNat owner.val = calldataWord I.calldata 4 := by
    have same := keyValueToWord_address_of_canonical _ checks.canonical
    rw [keyValueToWord_address] at same
    exact same
  have sourceChecks := withdrawal_checks_to_source sourceInitial owner amount ownerBinding rfl
    ((withdrawal_checks_equiv I maps).mp checks)
  have dispatched := source_selector_dispatch I ⟨2, by decide⟩ (by have := checks.length; omega) selector
  have decoded := withdrawal_abi_decode I checks.length checks.signedBound checks.canonical
  obtain ⟨paid, after, data, call, environment, run⟩ := withdrawal_bytecode_checked_call
    (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g)
    code writable bounded selector checks
  obtain ⟨sourceAccounts, sourceSubstate, sourceCall, afterMaps⟩ :=
    callViaEVM_accountMapEquiv (storage := config.storage)
      (evm_solm := withdrawalLockedState sourceInitial) call
      (by simpa only [withdrawal_locked_state, sourceInitial, initial, initState] using
        accountMapEquiv_sstoreAccountMap I.codeOwner ⟨6⟩ ⟨1⟩ maps)
      (by simp only [withdrawal_locked_state, sourceInitial, initState])
      (by simp only [withdrawal_locked_state, sourceInitial, initState])
      (by simp only [withdrawal_locked_state, sourceInitial, initState])
      (by simp only [withdrawal_locked_state, sourceInitial, initState])
      (by simp only [withdrawal_locked_state, sourceInitial, initState])
      (by simp only [withdrawal_locked_state, sourceInitial, initState])
  let sourceAfter := { withdrawalLockedState sourceInitial with
    accountMap := sourceAccounts
    substate := sourceSubstate
    createdAccounts := after.createdAccounts }
  have source := withdrawal_body_payment sourceInitial sourceAfter owner amount paid data sourceChecks sourceCall
  cases paid
  · have equivalent := run.reEquivExecutionRevert code dispatched decoded source
    simpa [Sat256.ofUInt256, Sat256.toUInt256] using equivalent
  · rcases run with failed | ⟨finalState, result, accounts⟩
    · exact reEquiv_outOfGas (Xi_error_of_X (g := g) (by
        rw [← code] at failed
        simpa [Sat256.ofUInt256] using failed))
    · have actual := Xi_success_of_X (g := g) (by
        rw [← code] at result
        simpa [Sat256.ofUInt256] using result)
      have sourceEnvironment : sourceAfter.executionEnv = sourceInitial.executionEnv := by
        simp only [sourceAfter, withdrawal_locked_state]
      have accountEq : finalState.accountMap = withdrawalOutputAccounts σ after.accountMap I :=
        congrArg Prod.snd accounts
      have createdEq : finalState.createdAccounts =
          (withdrawalFinalState sourceInitial sourceAfter owner amount).createdAccounts := by
        simpa only [withdrawalFinalState, withdrawalDebitedState, storageStore_createdAccounts,
          sourceAfter] using congrArg Prod.fst accounts
      have equivalent : accountMapEquiv finalState.accountMap
          (withdrawalFinalState sourceInitial sourceAfter owner amount).accountMap := by
        rw [accountEq, withdrawal_accounts_correspondence sourceInitial sourceAfter owner amount
          ownerBinding rfl sourceEnvironment sourceChecks.covered]
        exact withdrawal_output_accounts_equiv I maps afterMaps
      refine reEquiv_execution dispatched decoded source ?_
      rw [actual]
      exact execResultsEquiv.success rfl rfl createdEq equivalent
        (.abi (.fallthrough rfl rfl (by
          change encodeReturnValues? [] [] = some ByteArray.empty
          simp [encodeReturnValues?, encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?]
          rfl)))

end Rollup.EVM
