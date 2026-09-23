import semantics.ExecutionTree
import proofs.RollupCallOpcode
import proofs.CreationSite

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- An instruction's decoded call and selected code determine one child entry. -/
theorem child_call_entry_unique {jumps : Array UInt256} {before left right : Ethereum.State}
    (first : ChildCallEntry jumps before left) (second : ChildCallEntry jumps before right) : left = right := by
  cases first with
  | @entered op arg checked cost site code instruction precheck arguments enabled selected =>
    cases second with
    | @entered op' arg' checked' cost' site' code' instruction' precheck' arguments' enabled' selected' =>
      have sameOp := Prod.mk.inj (instruction.symm.trans instruction')
      rcases sameOp with ⟨rfl, rfl⟩
      have sameCheck := Prod.mk.inj (Except.ok.inj (precheck.symm.trans precheck'))
      rcases sameCheck with ⟨rfl, rfl⟩
      have sameSite := Option.some.inj (arguments.symm.trans arguments')
      subst site'
      have sameCode := ToExecute.Code.inj (selected.symm.trans selected')
      subst code'
      rfl

/-- An instruction's decoded creation arguments and guards determine one initialization entry. -/
theorem child_creation_entry_unique {jumps : Array UInt256} {before left right : Ethereum.State}
    (first : ChildCreationEntry jumps before left) (second : ChildCreationEntry jumps before right) : left = right := by
  cases first with
  | @entered op arg checked cost site instruction precheck arguments nonce allowed =>
    cases second with
    | @entered op' arg' checked' cost' site' instruction' precheck' arguments' nonce' allowed' =>
      have sameOp := Prod.mk.inj (instruction.symm.trans instruction')
      rcases sameOp with ⟨rfl, rfl⟩
      have sameCheck := Prod.mk.inj (Except.ok.inj (precheck.symm.trans precheck'))
      rcases sameCheck with ⟨rfl, rfl⟩
      have sameSite := Option.some.inj (arguments.symm.trans arguments')
      subst site'
      rfl

/-- One opcode cannot enter both a message frame and an initialization frame. -/
theorem child_entries_exclusive {jumps : Array UInt256} {before callChild creationChild : Ethereum.State}
    (call : ChildCallEntry jumps before callChild) (creation : ChildCreationEntry jumps before creationChild) : False := by
  cases call with
  | entered instruction precheck arguments enabled selected =>
    cases creation with
    | entered instruction' precheck' arguments' nonce allowed =>
      have sameOp := Prod.mk.inj (instruction.symm.trans instruction')
      rcases sameOp with ⟨rfl, rfl⟩
      have callKind := call_opcode_kind arguments
      have creationKind := creation_opcode_kind arguments'
      rcases callKind with rfl | rfl | rfl | rfl
      all_goals rcases creationKind with same | same <;> cases same

end Rollup.EVM
