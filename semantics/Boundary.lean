import semantics.MessageCall

open Ethereum

namespace Rollup.EVM

/-- Read the rollup account between calls, without execution metadata. -/
def accountView (self : Address) (accounts : AccountMap) : Ethereum.State :=
  { (default : Ethereum.State) with
    accountMap := accounts
    executionEnv.codeOwner := self
    executionEnv.code := runtimeBytecode }

def boundaryModel (self : Address) (accounts : AccountMap) (keys : AccessScope) : Rollup.State :=
  project (accountView self accounts) self keys

/-- Conditions to carry from one completed call to the next. -/
def BoundaryReady (self : Address) (accounts : AccountMap) (keys : AccessScope) : Prop :=
  OwnCode (accountView self accounts) ∧ WorldBounded (accountView self accounts) ∧
  StorageReady (accountView self accounts) self keys ∧
  readWord (accountView self accounts) self ⟨6⟩ = ⟨0⟩

/-- The runtime starts after the incoming ETH transfer. -/
noncomputable def MessageCall.entryState (call : MessageCall) : Ethereum.State :=
  { (default : Ethereum.State) with
    accountMap := call.initialAccounts
    σ₀ := call.original
    executionEnv := call.environment runtimeBytecode
    substate := call.substate
    createdAccounts := call.created
    machineState.gasAvailable := .ofUInt256 call.gas
    blocks := call.blocks
    genesisBlockHeader := call.genesis }

/-- Select code from the current account map, as the EVM does. -/
noncomputable def MessageCall.selectedRun (call : MessageCall) :=
  Ethereum.EVM.Θ call.blobs call.created call.genesis call.blocks call.accounts call.original
    call.substate call.sender call.origin call.receiver (toExecute call.accounts call.receiver)
    call.gas call.gasPrice call.value call.contextValue call.calldata call.depth call.header call.writable

end Rollup.EVM
