import proofs.support.ControlCertificate

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- Check successor indices directly instead of searching the candidate table. -/
def indexedControlRow (code : ByteArray) (table : Array AbstractCursor)
    (cursor : AbstractCursor) (indices : List Nat) : Bool :=
  let instruction := (decode code cursor.pc).getD (.STOP, none)
  cursor.controlSuccessors instruction.1 instruction.2 ==
    some (indices.filterMap fun index => table[index]?)

/-- Check one candidate row by its table index. -/
def indexedControlAt (code : ByteArray) (table : Array AbstractCursor)
    (edges : Array (List Nat)) (index : Nat) : Bool :=
  match table[index]?, edges[index]? with
  | some cursor, some indices => indexedControlRow code table cursor indices
  | _, _ => false

/-- Check an indexed certificate for every candidate row. -/
def indexedControlClosed (code : ByteArray) (table : Array AbstractCursor)
    (edges : Array (List Nat)) : Bool :=
  (List.range table.size).all (indexedControlAt code table edges)

end Rollup.EVM
