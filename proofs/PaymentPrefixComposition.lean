import proofs.support.PaymentPrefix
import semantics.CallScope
import proofs.WithdrawalPrefixBinding

open Ethereum Ethereum.EVM Reasoning.Theory

namespace Rollup.EVM

/-- A checked payment cursor binds custody to the active receiver, without a final-success premise. -/
theorem withdrawal_cursor_active_safe (start cursor child current : Ethereum.State)
    (keys : AccessScope) (jumps : Array UInt256)
    (code : OwnCode start) (world : WorldBounded start)
    (ready : StorageReady start start.executionEnv.codeOwner keys)
    (safe : Safe (project start start.executionEnv.codeOwner keys))
    (covered : CalldataCovered start keys) (bound : WithdrawalCallPrefix start cursor)
    (entered : ChildCallEntry jumps cursor child) (trace : ActivePrefix child current) :
    ∃ owner : Address,
      UInt256.ofNat owner.val = calldataWord start.executionEnv.calldata 4 ∧
      Safe (inFlightProjection current start.executionEnv.codeOwner keys
        ⟨owner, (calldataWord start.executionEnv.calldata 36).toNat,
          (project start start.executionEnv.codeOwner keys).eth⟩) := by
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
  refine ⟨owner, binding, ?_⟩
  apply withdrawal_call_active_safe start cursor child current owner (calldataWord start.executionEnv.calldata 36)
    gas ⟨128⟩ ⟨0⟩ ⟨128⟩ ⟨0⟩ _ keys jumps code world ready safe tracked binding rfl checks
    (accounts := by simpa only [withdrawalLockedState, storageStore_accountMap] using accounts) (context := congrArg ExecutionEnv.codeOwner environment)
    (decoded := decoded) (entered := entered) (trace := trace)
  simpa only [binding] using stack

end Rollup.EVM
