import semantics.CallOpcode

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- Enter a code child after the instruction precheck and the call guard succeed. -/
inductive ChildCallEntry (jumps : Array UInt256) (before : Ethereum.State) : Ethereum.State → Prop where
  | entered {op : Operation} {arg : Option (UInt256 × Nat)}
      {checked : Ethereum.State} {cost : Nat} {site : CallSite} {code : ByteArray}
      (instruction : (decode before.executionEnv.code before.machineState.pc).getD (.STOP, none) = (op, arg))
      (precheck : Z jumps op before = .ok (checked, cost))
      (arguments : CallSite.decode { checked with executionEnv.depth := before.executionEnv.depth }
        cost op = some site)
      (enabled : site.enabled (callParent { checked with executionEnv.depth := before.executionEnv.depth }))
      (selected : toExecute checked.accountMap (AccountAddress.ofUInt256 site.target) = .Code code) :
      ChildCallEntry jumps before
        ((site.message (callParent { checked with executionEnv.depth := before.executionEnv.depth })).codeEntry code)

end Rollup.EVM
