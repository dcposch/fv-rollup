import proofs.support.PrefixCursor

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- An exact prefix cursor bound to one code image and a known future code child. -/
def PCR (code : ByteArray) (environment : ExecutionEnv) (target child : Ethereum.State)
    (pc : UInt256) (stack : List UInt256) (memory : ByteArray) (words : UInt256) (returnData : ByteArray)
    (accounts : Batteries.RBSet AccountAddress compare × AccountMap) : Prop :=
  environment.code = code ∧
    PrefixCursor environment target child ⟨pc, stack, memory, words, returnData, accounts⟩

end Rollup.EVM
