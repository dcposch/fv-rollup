import proofs.support.ControlCertificate

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- A checked row supplies all supported control successors. -/
theorem control_certificate_row {code : ByteArray} {table : Array AbstractCursor}
    {cursor : AbstractCursor} (checked : controlClosedAt code table cursor = true) :
    ∃ next,
      cursor.controlSuccessors ((decode code cursor.pc).getD (.STOP, none)).1
        ((decode code cursor.pc).getD (.STOP, none)).2 = some next ∧
      ∀ following ∈ next, following ∈ table := by
  unfold controlClosedAt at checked
  cases result : cursor.controlSuccessors ((decode code cursor.pc).getD (.STOP, none)).1
      ((decode code cursor.pc).getD (.STOP, none)).2 with
  | none => simp [result] at checked
  | some next =>
    refine ⟨next, rfl, ?_⟩
    simpa [result] using checked

/-- A checked child row permits only CALL at the withdrawal instruction. -/
theorem control_certificate_call {code : ByteArray} {cursor : AbstractCursor}
    {op : Operation} {arg : Option (UInt256 × Nat)}
    (checked : controlChildAt code cursor = true)
    (decoded : (decode code cursor.pc).getD (.STOP, none) = (op, arg))
    (kind : op = .CALL ∨ op = .CALLCODE ∨ op = .DELEGATECALL ∨ op = .STATICCALL) :
    op = .CALL ∧ cursor.pc = ⟨935⟩ := by
  unfold controlChildAt at checked
  rw [decoded] at checked
  rcases kind with rfl | rfl | rfl | rfl
  · exact ⟨rfl, beq_iff_eq.mp checked⟩
  all_goals contradiction

end Rollup.EVM
