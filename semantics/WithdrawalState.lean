import semantics.Storage

namespace Rollup.EVM

def withdrawalLockedState (evm : Ethereum.State) : Ethereum.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨6⟩ ⟨1⟩

end Rollup.EVM
