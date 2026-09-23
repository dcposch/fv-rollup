import proofs.support.AbstractCursor

open Ethereum Ethereum.EVM

namespace Rollup.EVM
namespace AbstractCursor

/-- Replace an instruction's input words with unrestricted output words. -/
def replacePrefix (cursor : AbstractCursor) (inputs outputs : Nat) : Option AbstractCursor :=
  if inputs ≤ cursor.stack.length then
    some (cursor.advance (List.replicate outputs .any ++ cursor.stack.drop inputs))
  else none

/-- Track control flow without assuming that the lock is set. -/
def controlSuccessors (cursor : AbstractCursor) (op : Operation) (arg : Option (UInt256 × Nat)) :
    Option (List AbstractCursor) :=
  match op with
  | .NOT => (cursor.unary (AbstractWord.unary UInt256.lnot)).map List.singleton
  | .SLOAD => (cursor.unary (fun _ => .any)).map List.singleton
  | .ADDRESS | .CALLER | .GAS | .RETURNDATASIZE => some [cursor.push .any]
  | .SSTORE => (cursor.drop 2).map List.singleton
  | .RETURNDATACOPY => (cursor.drop 3).map List.singleton
  | .CALL => (cursor.replacePrefix 7 1).map List.singleton
  | _ => cursor.successors op arg

end AbstractCursor
end Rollup.EVM
