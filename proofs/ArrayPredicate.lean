import proofs.support.ArrayPredicate
import Mathlib

namespace Rollup.EVM

/-- Complete checked chunks establish a predicate for every array item. -/
theorem array_predicate_chunks_sound {α : Type} {table : Array α} {predicate : α → Bool}
    (chunks : List (List Nat)) (complete : chunks.flatten = List.range table.size)
    (checked : chunks.all (fun chunk => chunk.all (arrayPredicateAt table predicate)) = true) :
    table.all predicate = true := by
  apply Array.all_iff_forall.mpr
  intro index bounded range
  have member : index ∈ chunks.flatten := by
    rw [complete]
    exact List.mem_range.mpr bounded
  obtain ⟨chunk, inChunks, inChunk⟩ := List.mem_flatten.mp member
  have row := List.all_eq_true.mp (List.all_eq_true.mp checked chunk inChunks) index inChunk
  simpa only [arrayPredicateAt, Array.getElem?_eq_getElem bounded] using row

end Rollup.EVM
