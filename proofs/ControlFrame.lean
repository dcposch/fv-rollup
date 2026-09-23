import proofs.support.ControlFrame
import proofs.ControlPaths
import proofs.ControlCertificate
import proofs.ControlInstruction
import proofs.RollupCallOpcode
import semantics.ChildCall

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- The checked control table covers a fresh runtime frame. -/
theorem control_frame_initial {state : Ethereum.State}
    (code : state.executionEnv.code = runtimeBytecode) (counter : state.machineState.pc = ⟨0⟩)
    (stack : state.machineState.stack = []) : ControlFrameReady state := by
  refine ⟨code, ⟨⟨0⟩, []⟩, control_paths_initial, counter, ?_⟩
  change List.Forall₂ AbstractWord.denotes [] state.machineState.stack
  rw [stack]
  exact List.Forall₂.nil

/-- Every continuing runtime instruction stays in the checked control table. -/
theorem control_frame_step {before after : Ethereum.State} {jumps : Array UInt256}
    (ready : ControlFrameReady before) (run : Xstep jumps before = .ok (after, none)) :
    ControlFrameReady after := by
  obtain ⟨code, cursor, member, represented⟩ := ready
  have checked : controlClosedAt runtimeBytecode controlPaths cursor = true := by
    obtain ⟨index, bounded, same⟩ := Array.mem_iff_getElem.mp member
    rw [← same]
    have all := (Array.all_iff_forall.mp control_paths_closed) index bounded ⟨Nat.zero_le _, bounded⟩
    exact all
  obtain ⟨next, advance, closed⟩ := control_certificate_row checked
  have actualAdvance : cursor.controlSuccessors
      ((decode before.executionEnv.code cursor.pc).getD (.STOP, none)).1
      ((decode before.executionEnv.code cursor.pc).getD (.STOP, none)).2 = some next := by
    rw [code]
    exact advance
  obtain ⟨following, nextMember, known⟩ := control_instruction_sound represented actualAdvance run
  have environment := Xstep_env_unchanged before after jumps none run
  refine ⟨?_, following, closed following nextMember, known⟩
  exact (congrArg ExecutionEnv.code environment).symm.trans code

/-- Every actual continuing prefix retains a represented control cursor. -/
theorem control_prefix_ready {start current : Ethereum.State} {jumps : Array UInt256}
    (initial : ControlFrameReady start) (trace : ContinuingPrefix jumps start current) :
    ControlFrameReady current := by
  induction trace with
  | initial => exact initial
  | next earlier run ih =>
    obtain ⟨code, cursor, member, represented⟩ := control_frame_step ih run
    exact ⟨code, cursor, member, represented⟩

/-- An actual runtime child call can start only at the withdrawal CALL. -/
theorem control_frame_call_position {before child : Ethereum.State} {jumps : Array UInt256}
    (ready : ControlFrameReady before) (entered : ChildCallEntry jumps before child) :
    before.machineState.pc = ⟨935⟩ := by
  obtain ⟨code, cursor, member, represented⟩ := ready
  have checked : controlChildAt runtimeBytecode cursor = true := by
    obtain ⟨index, bounded, same⟩ := Array.mem_iff_getElem.mp member
    rw [← same]
    exact (Array.all_iff_forall.mp control_paths_children) index bounded ⟨Nat.zero_le _, bounded⟩
  cases entered with
  | entered instruction precheck arguments enabled selected =>
    rw [code, represented.1] at instruction
    have permitted := control_certificate_call checked instruction (call_opcode_kind arguments)
    exact represented.1.trans permitted.2

/-- Every outgoing runtime code call is reached at byte 935, including failing parent executions. -/
theorem runtime_call_prefix_position {start before child : Ethereum.State} {jumps : Array UInt256}
    (code : start.executionEnv.code = runtimeBytecode) (counter : start.machineState.pc = ⟨0⟩)
    (stack : start.machineState.stack = []) (trace : ContinuingPrefix jumps start before)
    (entered : ChildCallEntry jumps before child) : before.machineState.pc = ⟨935⟩ :=
  control_frame_call_position (control_prefix_ready (control_frame_initial code counter stack) trace) entered

end Rollup.EVM
