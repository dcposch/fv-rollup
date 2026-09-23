import proofs.ChildEntryUnique
import proofs.PrecheckCursor
import proofs.WorldPrecheck

open Ethereum Ethereum.EVM Reasoning.Theory

namespace Rollup.EVM

/-- An active CALL child has the target and value on the actual operand stack. -/
theorem call_child_binding {before child : Ethereum.State} {jumps : Array UInt256}
    (owner : Address) (value gas inOffset inSize outOffset outSize : UInt256) (rest : List UInt256)
    (decoded : (decode before.executionEnv.code before.machineState.pc).getD (.STOP, none) = (.CALL, none))
    (stack : before.machineState.stack = gas :: UInt256.ofNat owner.val :: value ::
      inOffset :: inSize :: outOffset :: outSize :: rest)
    (entered : ChildCallEntry jumps before child) :
    ∃ call : MessageCall, ∃ code : ByteArray,
      call.accounts = before.accountMap ∧ call.sender = before.executionEnv.codeOwner ∧
      call.receiver = owner ∧ call.value = value ∧
      toExecute call.accounts call.receiver = .Code code ∧ child = call.codeEntry code := by
  cases entered with
  | @entered op arg checked cost site code instruction precheck arguments enabled selected =>
    have operation := Prod.mk.inj (instruction.symm.trans decoded)
    rcases operation with ⟨rfl, rfl⟩
    have checkedStack := (precheck_cursor precheck).2.trans stack
    simp only [CallSite.decode, checkedStack] at arguments
    cases Option.some.inj arguments
    refine ⟨_, code, precheck_accounts precheck, ?_, ?_, rfl, ?_, rfl⟩
    · change AccountAddress.ofUInt256 (UInt256.ofNat checked.executionEnv.codeOwner.val) = _
      rw [accountAddress_roundtrip, Z_executionEnv_eq precheck]
    · exact accountAddress_roundtrip owner
    · simpa only [CallSite.message, accountAddress_roundtrip] using selected

end Rollup.EVM
