import semantics.Bindings
import Reasoning.Solc

open Ethereum Reasoning.Theory

namespace Rollup.EVM

/-- Read the mapping keys selected by the calldata. -/
def calldataScope (env : ExecutionEnv) : AccessScope :=
  if solcSelectorWord env = ⟨0x88af9950⟩ then
    {.pending (AccountAddress.ofNat (calldataWord env.calldata 100).toNat),
      .claims (AccountAddress.ofNat (calldataWord env.calldata 164).toNat)}
  else if solcSelectorWord env = ⟨0xf340fa01⟩ ∨ solcSelectorWord env = ⟨0xeb3349b9⟩ then
    {.pending (AccountAddress.ofNat (calldataWord env.calldata 4).toNat)}
  else if solcSelectorWord env = ⟨0xbb3ef682⟩ ∨ solcSelectorWord env = ⟨0xf3f43703⟩ then
    {.claims (AccountAddress.ofNat (calldataWord env.calldata 4).toNat)}
  else ∅

/-- Include the finite mapping-key set read from this calldata. -/
def CalldataCovered (evm : Ethereum.State) (keys : AccessScope) : Prop :=
  calldataScope evm.executionEnv ⊆ keys

end Rollup.EVM
