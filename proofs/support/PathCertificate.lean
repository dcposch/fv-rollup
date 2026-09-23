import proofs.support.AbstractCursor

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- Check that each abstract successor belongs to the supplied finite table. -/
def pathClosedAt (code : ByteArray) (table : Array AbstractCursor) (cursor : AbstractCursor) : Bool :=
  let instruction := (decode code cursor.pc).getD (.STOP, none)
  match cursor.successors instruction.1 instruction.2 with
  | none => false
  | some next => next.all table.contains

end Rollup.EVM
