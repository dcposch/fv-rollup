import proofs.WithdrawalSelectedPrefix
import proofs.WithdrawalCheckCorrespondence
import proofs.CallChildBinding

open Ethereum Ethereum.EVM Reasoning.Theory

namespace Rollup.EVM

/-- Prelude checks and custody establish a funded withdrawal without assuming final success. -/
theorem withdrawal_checks_enabled (before : Ethereum.State) (owner : Address) (value : UInt256)
    (keys : AccessScope) (code : OwnCode before)
    (ready : StorageReady before before.executionEnv.codeOwner keys)
    (safe : Safe (project before before.executionEnv.codeOwner keys))
    (tracked : StorageKey.claims owner ∈ keys)
    (ownerBinding : UInt256.ofNat owner.val = calldataWord before.executionEnv.calldata 4)
    (amountBinding : value = calldataWord before.executionEnv.calldata 36)
    (checks : WithdrawalBytecodeChecks before.accountMap before.executionEnv) :
    WithdrawalEnabled (project before before.executionEnv.codeOwner keys) owner value.toNat := by
  have sourceChecks := withdrawal_checks_to_source before owner value.toNat ownerBinding
    (congrArg UInt256.toNat amountBinding) checks
  have credit := withdrawal_credit_model before owner keys code ready tracked
  exact credited_withdrawal_has_funds safe rfl (Nat.pos_of_ne_zero sourceChecks.positive)
    (by simpa only [credit] using sourceChecks.covered)

/-- The actual child of a checked withdrawal CALL remains safe even if the parent later fails. -/
theorem withdrawal_call_active_safe (before cursor child current : Ethereum.State)
    (owner : Address) (value gas inOffset inSize outOffset outSize : UInt256)
    (rest : List UInt256) (keys : AccessScope) (jumps : Array UInt256)
    (code : OwnCode before) (world : WorldBounded before)
    (ready : StorageReady before before.executionEnv.codeOwner keys)
    (safe : Safe (project before before.executionEnv.codeOwner keys))
    (tracked : StorageKey.claims owner ∈ keys)
    (ownerBinding : UInt256.ofNat owner.val = calldataWord before.executionEnv.calldata 4)
    (amountBinding : value = calldataWord before.executionEnv.calldata 36)
    (checks : WithdrawalBytecodeChecks before.accountMap before.executionEnv)
    (accounts : cursor.accountMap = (withdrawalLockedState before).accountMap)
    (context : cursor.executionEnv.codeOwner = before.executionEnv.codeOwner)
    (decoded : (decode cursor.executionEnv.code cursor.machineState.pc).getD (.STOP, none) = (.CALL, none))
    (stack : cursor.machineState.stack = gas :: UInt256.ofNat owner.val :: value ::
      inOffset :: inSize :: outOffset :: outSize :: rest)
    (entered : ChildCallEntry jumps cursor child) (trace : ActivePrefix child current) :
    Safe (inFlightProjection current before.executionEnv.codeOwner keys
      ⟨owner, value.toNat, (project before before.executionEnv.codeOwner keys).eth⟩) := by
  have enabled := withdrawal_checks_enabled before owner value keys code ready safe tracked
    ownerBinding amountBinding checks
  obtain ⟨call, selectedCode, callAccounts, sender, receiver, amount, selected, entry⟩ :=
    call_child_binding owner value gas inOffset inSize outOffset outSize rest decoded stack entered
  rw [entry] at trace
  exact withdrawal_selected_active_safe before current owner value keys call selectedCode code world ready safe
    enabled (callAccounts.trans accounts) (sender.trans context) receiver amount selected trace

end Rollup.EVM
