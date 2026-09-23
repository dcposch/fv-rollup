import semantics.CreationSite
import semantics.ExecutionPrefix

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- Enter initialization after the actual instruction checks and creation guards. -/
inductive ChildCreationEntry (jumps : Array UInt256) (before : Ethereum.State) : Ethereum.State → Prop where
  | entered {op : Operation} {arg : Option (UInt256 × Nat)}
      {checked : Ethereum.State} {cost : Nat} {site : CreationSite}
      (instruction : (decode before.executionEnv.code before.machineState.pc).getD (.STOP, none) = (op, arg))
      (precheck : Z jumps op before = .ok (checked, cost))
      (arguments : CreationSite.decode { checked with executionEnv.depth := before.executionEnv.depth }
        op = some site)
      (bounded : (checked.accountMap.findD checked.executionEnv.codeOwner default).nonce.toNat < 2 ^ 64 - 1)
      (allowed : site.guard { checked with executionEnv.depth := before.executionEnv.depth }) :
      ChildCreationEntry jumps before
        (site.call { checked with executionEnv.depth := before.executionEnv.depth } cost allowed).entryState

end Rollup.EVM
