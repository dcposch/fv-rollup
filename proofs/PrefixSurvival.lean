import proofs.ExecutionSurvival
import semantics.ActivePrefix

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- An actual instruction preserves account survival without a supplied child record. -/
theorem instruction_survives {before after : Ethereum.State} {jumps : Array UInt256} {ret}
    {self : Address} (initial : StateSurvives self before)
    (run : Xstep jumps before = .ok (after, ret)) : StateSurvives self after := by
  rcases decoded : (decode before.executionEnv.code before.machineState.pc).getD (.STOP, none) with ⟨op, arg⟩
  by_cases internal : LocalOperation op
  · exact local_instruction_survives initial internal decoded run
  · have frames : ChildFramesSurvive self jumps before :=
      fun child _ survived => execution_survives _ _ child survived
    rcases nonlocal_operation_cases internal with calls | creations | rfl
    · exact call_instruction_survives initial decoded calls frames run
    · exact creation_instruction_survives initial decoded creations frames run
    · exact selfdestruct_instruction_survives initial decoded run

/-- Account survival holds before every instruction in a continuing frame. -/
theorem continuing_prefix_survives {start current : Ethereum.State} {jumps : Array UInt256}
    {self : Address} (initial : StateSurvives self start)
    (trace : ContinuingPrefix jumps start current) : StateSurvives self current := by
  induction trace with
  | initial => exact initial
  | next earlier run ih =>
    have effect := instruction_survives ih run
    exact effect

/-- Account survival holds on both sides of each completed instruction. -/
theorem instruction_prefix_survives {start current : Ethereum.State} {jumps : Array UInt256}
    {self : Address} (initial : StateSurvives self start)
    (trace : InstructionPrefix jumps start current) : StateSurvives self current := by
  cases trace with
  | current earlier => exact continuing_prefix_survives initial earlier
  | afterStep earlier run => exact instruction_survives (continuing_prefix_survives initial earlier) run

/-- Entering an actual call child preserves account survival. -/
theorem child_call_entry_survives {before child : Ethereum.State} {jumps : Array UInt256}
    {self : Address} (initial : StateSurvives self before)
    (entered : ChildCallEntry jumps before child) : StateSurvives self child := by
  cases entered with
  | @entered op arg checked cost site code instruction precheck arguments enabled selected =>
    have checkedSurvives := precheck_survives initial precheck
    exact message_entry_survives _ code
      (call_site_initial_survives site
        (callParent { checked with executionEnv.depth := before.executionEnv.depth }) checkedSurvives)

/-- Entering actual initialization preserves account survival. -/
theorem child_creation_entry_survives {before child : Ethereum.State} {jumps : Array UInt256}
    {self : Address} (initial : StateSurvives self before)
    (entered : ChildCreationEntry jumps before child) : StateSurvives self child := by
  cases entered with
  | @entered op arg checked cost site instruction precheck arguments bounded allowed =>
    have checkedSurvives := precheck_survives initial precheck
    exact creation_entry_survives _ (nonce_survives checkedSurvives)

/-- Account survival holds inside active call chains, including frames that later revert. -/
theorem active_prefix_survives {start current : Ethereum.State} {self : Address}
    (initial : StateSurvives self start) (trace : ActivePrefix start current) : StateSurvives self current := by
  induction trace with
  | within earlier => exact instruction_prefix_survives initial earlier
  | call earlier entered later ih =>
    exact ih (child_call_entry_survives (continuing_prefix_survives initial earlier) entered)
  | creation earlier entered later ih =>
    exact ih (child_creation_entry_survives (continuing_prefix_survives initial earlier) entered)

end Rollup.EVM
