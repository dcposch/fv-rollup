import proofs.support.PathCertificate
import proofs.AbstractCursor

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- A checked table row gives a supported instruction and all its successors. -/
theorem path_certificate_row {code : ByteArray} {table : Array AbstractCursor}
    {cursor : AbstractCursor} (checked : pathClosedAt code table cursor = true) :
    ∃ next,
      cursor.successors ((decode code cursor.pc).getD (.STOP, none)).1
        ((decode code cursor.pc).getD (.STOP, none)).2 = some next ∧
      ∀ following ∈ next, following ∈ table := by
  unfold pathClosedAt at checked
  cases result : cursor.successors ((decode code cursor.pc).getD (.STOP, none)).1
      ((decode code cursor.pc).getD (.STOP, none)).2 with
  | none => simp [result] at checked
  | some next =>
    refine ⟨next, rfl, ?_⟩
    simpa [result] using checked

/-- A checked row cannot execute an account-changing opcode. -/
theorem path_certificate_neutral {code : ByteArray} {table : Array AbstractCursor}
    {cursor : AbstractCursor} (checked : pathClosedAt code table cursor = true) :
    AccountPreservingOperation ((decode code cursor.pc).getD (.STOP, none)).1 := by
  obtain ⟨next, supported, closed⟩ := path_certificate_row checked
  exact abstract_successors_neutral supported

end Rollup.EVM
