import semantics.Semantics

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- These opcodes can change machine state or substate, but cannot change accounts. -/
def AccountPreservingOperation : Operation → Prop
  | .CREATE | .CREATE2 | .CALL | .CALLCODE | .DELEGATECALL | .STATICCALL | .SELFDESTRUCT
  | .SSTORE | .TSTORE => False
  | _ => True

end Rollup.EVM
