import proofs.support.ControlCursor

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- Check all control successors against the finite candidate table. -/
def controlClosedAt (code : ByteArray) (table : Array AbstractCursor) (cursor : AbstractCursor) : Bool :=
  let instruction := (decode code cursor.pc).getD (.STOP, none)
  match cursor.controlSuccessors instruction.1 instruction.2 with
  | none => false
  | some next => next.all table.contains

/-- The runtime may enter a child only at its withdrawal CALL. -/
def controlChildAt (code : ByteArray) (cursor : AbstractCursor) : Bool :=
  match ((decode code cursor.pc).getD (.STOP, none)).1 with
  | .CALL => cursor.pc == ⟨935⟩
  | .CALLCODE | .DELEGATECALL | .STATICCALL | .CREATE | .CREATE2 => false
  | _ => true

end Rollup.EVM
