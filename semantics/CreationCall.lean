import semantics.Deployment
import Ethereum.Theory.AccountLocality

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- Inputs to a creation call, after the caller's nonce increment. -/
structure CreationCall extends Deployment where
  value : UInt256
  initCode : ByteArray
  writable : Bool

noncomputable def CreationCall.address (call : CreationCall) : Address :=
  call.toDeployment.address call.initCode

/-- A collision selects invalid code before any initialization instruction can run. -/
noncomputable def CreationCall.collision (call : CreationCall) : Bool :=
  let old := call.accounts.findD call.address default
  old.nonce ≠ ⟨0⟩ || old.code.size ≠ 0 || old.storage != default

noncomputable def CreationCall.initialAccounts (call : CreationCall) : AccountMap :=
  sendEthCreate call.address call.sender call.value true call.accounts

noncomputable def CreationCall.initialCreated (call : CreationCall) :=
  if call.collision then call.created else call.created.insert call.address

noncomputable def CreationCall.environment (call : CreationCall) : ExecutionEnv :=
  { codeOwner := call.address
    sender := call.origin
    source := call.sender
    weiValue := call.value
    calldata := default
    code := if call.collision then ⟨#[0xfe]⟩ else call.initCode
    gasPrice := call.gasPrice.toNat
    header := call.header
    depth := call.depth
    perm := call.writable
    blobVersionedHashes := call.blobs }

noncomputable def CreationCall.entryState (call : CreationCall) : Ethereum.State :=
  { (default : Ethereum.State) with
    accountMap := call.initialAccounts
    σ₀ := call.original
    executionEnv := call.environment
    substate := call.substate.addAccessedAccount call.address
    createdAccounts := call.initialCreated
    machineState.gasAvailable := .ofUInt256 call.gas
    blocks := call.blocks
    genesisBlockHeader := call.genesis }

noncomputable def CreationCall.execute (call : CreationCall) :=
  Ξ call.initialCreated call.genesis call.blocks call.initialAccounts call.original call.gas
    (call.substate.addAccessedAccount call.address) call.environment

noncomputable def CreationCall.run (call : CreationCall) :=
  Lambda call.blobs call.created call.genesis call.blocks call.accounts call.original call.substate
    call.sender call.origin call.gas call.gasPrice call.value call.initCode call.depth call.salt
    call.header call.writable

end Rollup.EVM
