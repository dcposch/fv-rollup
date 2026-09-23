import semantics.MessageCall
import semantics.ExecutionPrefix

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- Inputs to the EVM call helper, before the nested call starts. -/
structure CallSite where
  gasCost : Nat
  blobs : List ByteArray
  gas : UInt256
  source : UInt256
  recipient : UInt256
  target : UInt256
  value : UInt256
  contextValue : UInt256
  inOffset : UInt256
  inSize : UInt256
  outOffset : UInt256
  outSize : UInt256
  writable : Bool

/-- The helper checks the current account balance and the call depth. -/
def CallSite.enabled (site : CallSite) (state : Ethereum.State) : Prop :=
  site.value ≤ (state.accountMap.find? state.executionEnv.codeOwner).option ⟨0⟩ (·.balance) ∧
    state.executionEnv.depth < 1024

/-- Bind the child message to the helper's arguments and the current EVM state. -/
noncomputable def CallSite.message (site : CallSite) (state : Ethereum.State) : MessageCall :=
  { blobs := site.blobs
    created := state.createdAccounts
    genesis := state.genesisBlockHeader
    blocks := state.blocks
    accounts := state.accountMap
    original := state.σ₀
    substate := (state.addAccessedAccount (AccountAddress.ofUInt256 site.target)).substate
    sender := AccountAddress.ofUInt256 site.source
    origin := state.executionEnv.sender
    receiver := AccountAddress.ofUInt256 site.recipient
    gas := .ofNat (Ccallgas (AccountAddress.ofUInt256 site.target)
      (AccountAddress.ofUInt256 site.recipient) site.value site.gas state.accountMap
      state.machineState state.substate)
    gasPrice := .ofNat state.executionEnv.gasPrice
    value := site.value
    contextValue := site.contextValue
    calldata := state.machineState.memory.readWithPadding site.inOffset.toNat site.inSize.toNat
    depth := state.executionEnv.depth + 1
    header := state.executionEnv.header
    writable := site.writable }

/-- The fresh execution state used by the code branch of the message call. -/
noncomputable def MessageCall.codeEntry (message : MessageCall) (code : ByteArray) : Ethereum.State :=
  { (default : Ethereum.State) with
    accountMap := message.initialAccounts
    σ₀ := message.original
    executionEnv := message.environment code
    substate := message.substate
    createdAccounts := message.created
    machineState.gasAvailable := .ofUInt256 message.gas
    blocks := message.blocks
    genesisBlockHeader := message.genesis }

/-- Select the child code at the target address. Its storage context can differ. -/
noncomputable def CallSite.outcome (site : CallSite) (state : Ethereum.State) :=
  let message := site.message state
  Θ message.blobs message.created message.genesis message.blocks message.accounts message.original
    message.substate message.sender message.origin message.receiver
    (toExecute state.accountMap (AccountAddress.ofUInt256 site.target))
    message.gas message.gasPrice message.value message.contextValue message.calldata message.depth
    message.header message.writable

/-- Run the EVM helper with these arguments. -/
noncomputable def CallSite.run (site : CallSite) (state : Ethereum.State) :=
  call site.gasCost site.blobs site.gas site.source site.recipient site.target site.value
    site.contextValue site.inOffset site.inSize site.outOffset site.outSize site.writable state

end Rollup.EVM
