import semantics.ExecutionTrace

namespace Rollup.EVM

def ExecutionEvent.keys (event : ExecutionEvent) : AccessScope :=
  match event with
  | .message call _ => calldataScope { (default : Ethereum.ExecutionEnv) with calldata := call.calldata }
  | .donation _ _ => ∅
  | .selfdestruct _ => ∅
  | .rejected _ _ => ∅

/-- Collect keys named by trace calldata, including rejected messages. -/
def executionScope : List ExecutionEvent → AccessScope
  | [] => fixedKeys
  | event :: events => event.keys ∪ executionScope events

end Rollup.EVM
