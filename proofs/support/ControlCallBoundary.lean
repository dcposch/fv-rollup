import proofs.support.ControlCertificate

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- Check that a CALL's successors lie in the supplied post-call region. -/
def controlCallToTable (code : ByteArray) (table : Array AbstractCursor) (cursor : AbstractCursor) : Bool :=
  match ((decode code cursor.pc).getD (.STOP, none)).1 with
  | .CALL => controlClosedAt code table cursor
  | _ => true

end Rollup.EVM
