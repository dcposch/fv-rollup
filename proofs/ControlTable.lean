import proofs.support.ControlTable
import proofs.ControlCertificate
import proofs.ControlInstruction

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- A closed control table covers each continuing instruction. -/
theorem control_table_step {code : ByteArray} {table : Array AbstractCursor}
    {before after : Ethereum.State} {jumps : Array UInt256}
    (closedTable : table.all (controlClosedAt code table) = true)
    (ready : ControlTableReady code table before) (run : Xstep jumps before = .ok (after, none)) :
    ControlTableReady code table after := by
  obtain ⟨codeEq, cursor, member, represented⟩ := ready
  have checked : controlClosedAt code table cursor = true := by
    obtain ⟨index, bounded, same⟩ := Array.mem_iff_getElem.mp member
    rw [← same]
    exact (Array.all_iff_forall.mp closedTable) index bounded ⟨Nat.zero_le _, bounded⟩
  obtain ⟨next, advance, closed⟩ := control_certificate_row checked
  have actualAdvance : cursor.controlSuccessors
      ((decode before.executionEnv.code cursor.pc).getD (.STOP, none)).1
      ((decode before.executionEnv.code cursor.pc).getD (.STOP, none)).2 = some next := by
    rw [codeEq]
    exact advance
  obtain ⟨following, nextMember, known⟩ := control_instruction_sound represented actualAdvance run
  have environment := Xstep_env_unchanged before after jumps none run
  refine ⟨?_, following, closed following nextMember, known⟩
  rwa [← environment]

/-- A closed control table covers the entire continuing prefix. -/
theorem control_table_prefix {code : ByteArray} {table : Array AbstractCursor}
    {start current : Ethereum.State} {jumps : Array UInt256}
    (closedTable : table.all (controlClosedAt code table) = true)
    (initial : ControlTableReady code table start) (trace : ContinuingPrefix jumps start current) :
    ControlTableReady code table current := by
  induction trace with
  | initial => exact initial
  | next earlier run ih =>
    obtain ⟨codeEq, cursor, member, represented⟩ := control_table_step closedTable ih run
    exact ⟨codeEq, cursor, member, represented⟩

/-- An excluded counter cannot occur on a prefix represented by a closed table. -/
theorem control_table_excludes {code : ByteArray} {table : Array AbstractCursor} {pc : UInt256}
    {start current : Ethereum.State} {jumps : Array UInt256}
    (closedTable : table.all (controlClosedAt code table) = true)
    (excluded : table.all (fun cursor => cursor.pc != pc) = true)
    (initial : ControlTableReady code table start) (trace : ContinuingPrefix jumps start current) :
    current.machineState.pc ≠ pc := by
  obtain ⟨codeEq, cursor, member, represented⟩ := control_table_prefix closedTable initial trace
  obtain ⟨index, bounded, same⟩ := Array.mem_iff_getElem.mp member
  have absent := (Array.all_iff_forall.mp excluded) index bounded ⟨Nat.zero_le _, bounded⟩
  rw [same] at absent
  rw [represented.1]
  simpa using absent

end Rollup.EVM
