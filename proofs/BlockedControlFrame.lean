import proofs.ControlFrame
import proofs.ControlTable
import proofs.BlockedControlPaths

open Ethereum Ethereum.EVM

set_option maxRecDepth 100000

namespace Rollup.EVM

/-- A non-withdrawal entry cannot reach the withdrawal CALL in the same frame. -/
theorem nonwithdraw_prefix_excludes_call {start current : Ethereum.State} {jumps : Array UInt256}
    (entry : RuntimeEntry) (different : entry ≠ .withdrawal) (selector : UInt256)
    (code : start.executionEnv.code = runtimeBytecode)
    (counter : start.machineState.pc = runtimeEntryPC entry)
    (stack : start.machineState.stack = [selector])
    (trace : ContinuingPrefix jumps start current) : current.machineState.pc ≠ ⟨935⟩ := by
  apply control_table_excludes blocked_control_paths_closed blocked_control_paths_exclude_call _ trace
  refine ⟨code, ⟨runtimeEntryPC entry, [.any]⟩, nonwithdraw_entry_blocked entry different, counter, ?_⟩
  change List.Forall₂ AbstractWord.denotes [.any] start.machineState.stack
  rw [stack]
  exact List.Forall₂.cons trivial List.Forall₂.nil

/-- Completing the runtime CALL establishes the checked post-call region. -/
theorem control_call_result_blocked {before after : Ethereum.State} {jumps : Array UInt256}
    (ready : ControlFrameReady before) (counter : before.machineState.pc = ⟨935⟩)
    (run : Xstep jumps before = .ok (after, none)) :
    ControlTableReady runtimeBytecode blockedControlPaths after := by
  obtain ⟨code, cursor, member, represented⟩ := ready
  have row : controlCallToTable runtimeBytecode blockedControlPaths cursor = true := by
    obtain ⟨index, bounded, same⟩ := Array.mem_iff_getElem.mp member
    rw [← same]
    exact (Array.all_iff_forall.mp control_call_enters_blocked) index bounded ⟨Nat.zero_le _, bounded⟩
  have cursorPC : cursor.pc = ⟨935⟩ := represented.1.symm.trans counter
  have decoded : ((decode runtimeBytecode cursor.pc).getD (.STOP, none)).1 = .CALL := by
    rw [cursorPC]
    decide +kernel
  change (match ((decode runtimeBytecode cursor.pc).getD (.STOP, none)).1 with
    | .CALL => controlClosedAt runtimeBytecode blockedControlPaths cursor
    | _ => true) = true at row
  rw [decoded] at row
  obtain ⟨next, advance, closed⟩ := control_certificate_row row
  have actualAdvance : cursor.controlSuccessors
      ((decode before.executionEnv.code cursor.pc).getD (.STOP, none)).1
      ((decode before.executionEnv.code cursor.pc).getD (.STOP, none)).2 = some next := by
    rw [code]
    exact advance
  obtain ⟨following, nextMember, known⟩ := control_instruction_sound represented actualAdvance run
  have environment := Xstep_env_unchanged before after jumps none run
  refine ⟨?_, following, closed following nextMember, known⟩
  exact (congrArg ExecutionEnv.code environment).symm.trans code

/-- The runtime cannot return to its outgoing CALL after that instruction completes. -/
theorem runtime_call_not_repeated {before after current : Ethereum.State} {jumps : Array UInt256}
    (ready : ControlFrameReady before) (counter : before.machineState.pc = ⟨935⟩)
    (run : Xstep jumps before = .ok (after, none))
    (trace : ContinuingPrefix jumps { after with executionEnv.depth := before.executionEnv.depth } current) :
    current.machineState.pc ≠ ⟨935⟩ := by
  obtain ⟨code, cursor, member, represented⟩ := control_call_result_blocked ready counter run
  have nextReady : ControlTableReady runtimeBytecode blockedControlPaths
      { after with executionEnv.depth := before.executionEnv.depth } :=
    ⟨code, cursor, member, represented⟩
  exact control_table_excludes blocked_control_paths_closed blocked_control_paths_exclude_call nextReady trace

end Rollup.EVM
