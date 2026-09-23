import proofs.WithdrawalSelectedStorage
import proofs.PaymentPrefixComposition

open Ethereum Ethereum.EVM Reasoning.Theory

namespace Rollup.EVM

/-- The actual payment cursor establishes storage isolation for its whole active receiver tree. -/
theorem withdrawal_cursor_active_storage (start cursor child current : Ethereum.State)
    (keys : AccessScope) (jumps : Array UInt256)
    (code : OwnCode start) (world : WorldBounded start)
    (ready : StorageReady start start.executionEnv.codeOwner keys)
    (safe : Safe (project start start.executionEnv.codeOwner keys))
    (covered : CalldataCovered start keys) (bound : WithdrawalCallPrefix start cursor)
    (entered : ChildCallEntry jumps cursor child) (trace : ActivePrefix child current) :
    CodeStorageFrame start.executionEnv.codeOwner (withdrawalLockedState start).accountMap current.accountMap := by
  obtain ⟨checks, selector, accounts, environment, counter, gas, stack⟩ := bound
  let owner : Address := ⟨(calldataWord start.executionEnv.calldata 4).toNat, checks.canonical⟩
  have binding : UInt256.ofNat owner.val = calldataWord start.executionEnv.calldata 4 :=
    u256_inj (Nat.mod_eq_of_lt (calldataWord start.executionEnv.calldata 4).val.isLt)
  have tracked : StorageKey.claims owner ∈ keys := by
    apply covered
    simp only [calldataScope, selector]
    have ownerEq : AccountAddress.ofNat (calldataWord start.executionEnv.calldata 4).toNat = owner := by
      apply Fin.ext
      exact Nat.mod_eq_of_lt checks.canonical
    simp [ownerEq]
  have decoded : (decode cursor.executionEnv.code cursor.machineState.pc).getD (.STOP, none) = (.CALL, none) := by
    rw [environment, code.1, counter]
    decide +kernel
  have paymentStack : cursor.machineState.stack = gas :: UInt256.ofNat owner.val ::
      calldataWord start.executionEnv.calldata 36 :: ⟨128⟩ :: ⟨0⟩ :: ⟨128⟩ :: ⟨0⟩ ::
      [⟨128⟩, calldataWord start.executionEnv.calldata 36, calldataWord start.executionEnv.calldata 4, ⟨0⟩,
        withdrawalClaimWord (sstoreAccountMap start.executionEnv.codeOwner start.accountMap ⟨6⟩ ⟨1⟩)
          start.executionEnv, calldataWord start.executionEnv.calldata 36,
        calldataWord start.executionEnv.calldata 4, ⟨226⟩, ⟨0xbb3ef682⟩] := by
    simpa only [binding] using stack
  obtain ⟨call, selectedCode, callAccounts, sender, receiver, amount, selected, entry⟩ :=
    call_child_binding owner (calldataWord start.executionEnv.calldata 36) gas
      ⟨128⟩ ⟨0⟩ ⟨128⟩ ⟨0⟩ _ decoded paymentStack entered
  have enabled := withdrawal_checks_enabled start owner (calldataWord start.executionEnv.calldata 36)
    keys code ready safe tracked binding rfl checks
  rw [entry] at trace
  apply withdrawal_selected_active_storage start current owner (calldataWord start.executionEnv.calldata 36)
    keys call selectedCode code world ready safe enabled _
    (sender.trans (congrArg ExecutionEnv.codeOwner environment)) receiver amount selected trace
  simpa only [withdrawalLockedState, storageStore_accountMap] using callAccounts.trans accounts

end Rollup.EVM
