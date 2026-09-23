import invariants.Invariants
import semantics.ExecutionTrace
import semantics.RootEntryPath

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- Bind a fresh root frame to its funded message and pre-transfer boundary. -/
def RootMessageOrigin (self : Address) (keys : AccessScope) (root : Ethereum.State) : Prop :=
  ∃ call : MessageCall,
    root = call.codeEntry runtimeBytecode ∧ MessageEnvironment self call ∧
    BoundaryReady self call.accounts keys ∧ Safe (boundaryModel self call.accounts keys)

end Rollup.EVM
