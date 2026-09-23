import proofs.support.IndexedControl

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- A checked index list certifies all abstract successors as table members. -/
theorem indexed_control_row_sound {code : ByteArray} {table : Array AbstractCursor}
    {cursor : AbstractCursor} {indices : List Nat}
    (checked : indexedControlRow code table cursor indices = true) :
    controlClosedAt code table cursor = true := by
  have same := beq_iff_eq.mp checked
  change cursor.controlSuccessors ((decode code cursor.pc).getD (.STOP, none)).1
    ((decode code cursor.pc).getD (.STOP, none)).2 =
      some (indices.filterMap fun index => table[index]?) at same
  unfold controlClosedAt
  dsimp only
  rw [same]
  apply List.all_eq_true.mpr
  intro following member
  obtain ⟨index, _, found⟩ := List.mem_filterMap.mp member
  simpa using Array.mem_of_getElem? found

/-- The kernel-checked index certificate implies full table closure. -/
theorem indexed_control_closed_sound {code : ByteArray} {table : Array AbstractCursor}
    {edges : Array (List Nat)} (checked : indexedControlClosed code table edges = true) :
    table.all (controlClosedAt code table) = true := by
  apply Array.all_iff_forall.mpr
  intro index bounded range
  have row := List.all_eq_true.mp checked index (List.mem_range.mpr bounded)
  change (match table[index]?, edges[index]? with
    | some cursor, some indices => indexedControlRow code table cursor indices
    | _, _ => false) = true at row
  rw [Array.getElem?_eq_getElem bounded] at row
  cases found : edges[index]? with
  | none => simp [found] at row
  | some indices =>
    simp only [found] at row
    exact indexed_control_row_sound row

/-- Checked finite chunks certify the same complete row list. -/
theorem indexed_control_chunks_sound {code : ByteArray} {table : Array AbstractCursor}
    {edges : Array (List Nat)} (chunks : List (List Nat))
    (complete : chunks.flatten = List.range table.size)
    (checked : chunks.all (fun chunk => chunk.all (indexedControlAt code table edges)) = true) :
    indexedControlClosed code table edges = true := by
  apply List.all_eq_true.mpr
  intro index member
  have combined : index ∈ chunks.flatten := by rwa [complete]
  obtain ⟨chunk, inChunks, inChunk⟩ := List.mem_flatten.mp combined
  exact List.all_eq_true.mp (List.all_eq_true.mp checked chunk inChunks) index inChunk

end Rollup.EVM
