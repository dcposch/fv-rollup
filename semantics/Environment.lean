import semantics.Storage
import semantics.Bytecode

namespace Rollup.EVM

/-- Bound total ETH to exclude word overflow during external transfers. -/
noncomputable def WorldBounded (evm : Ethereum.State) : Prop :=
  total (fun a => ((evm.lookupAccount a).elim (⟨0⟩ : Ethereum.UInt256)
    (fun acc => acc.balance)).toNat) < wordLimit

/-- Execute the pinned code in the rollup's own storage context. -/
def OwnCode (evm : Ethereum.State) : Prop :=
  evm.executionEnv.code = runtimeBytecode ∧
  (evm.lookupAccount evm.executionEnv.codeOwner).map (·.code) = some runtimeBytecode

end Rollup.EVM
