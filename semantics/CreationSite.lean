import semantics.CreationCall

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- Stack arguments shared by CREATE and CREATE2. -/
structure CreationSite where
  value : UInt256
  offset : UInt256
  size : UInt256
  salt : Option ByteArray

def CreationSite.decode (state : Ethereum.State) (op : Operation) : Option CreationSite :=
  match op with
  | .CREATE =>
    match state.machineState.stack.pop3 with
    | none => none
    | some (_, value, offset, size) => some ⟨value, offset, size, none⟩
  | .CREATE2 =>
    match state.machineState.stack.pop4 with
    | none => none
    | some (_, value, offset, size, salt) => some ⟨value, offset, size, some salt.toByteArray⟩
  | _ => none

def CreationSite.code (site : CreationSite) (state : Ethereum.State) : ByteArray :=
  state.machineState.memory.readWithPadding site.offset.toNat site.size.toNat

/-- The opcode checks funds, depth, and the initialization-code length. -/
def CreationSite.guard (site : CreationSite) (state : Ethereum.State) : Prop :=
  site.value ≤ (state.accountMap.find? state.executionEnv.codeOwner).option ⟨0⟩ (·.balance) ∧
    state.executionEnv.depth < 1024 ∧ (site.code state).size ≤ 49152

/-- Bind the creation call after charging gas and incrementing the caller's nonce. -/
noncomputable def CreationSite.call (site : CreationSite) (state : Ethereum.State) (cost : Nat)
    (allowed : site.guard state) : CreationCall :=
  { blobs := state.executionEnv.blobVersionedHashes
    created := state.createdAccounts
    genesis := state.genesisBlockHeader
    blocks := state.blocks
    accounts := state.accountMap.insert state.executionEnv.codeOwner
      { (state.accountMap.findD state.executionEnv.codeOwner default) with
        nonce := (state.accountMap.findD state.executionEnv.codeOwner default).nonce + ⟨1⟩ }
    original := state.σ₀
    substate := state.substate
    sender := state.executionEnv.codeOwner
    origin := state.executionEnv.sender
    gas := .ofNat (L (state.machineState.gasAvailable.subNat cost).toNat)
    gasPrice := .ofNat state.executionEnv.gasPrice
    depth := ⟨state.executionEnv.depth.val + 1, Nat.succ_lt_succ allowed.2.1⟩
    salt := site.salt
    header := state.executionEnv.header
    value := site.value
    initCode := site.code state
    writable := state.executionEnv.perm }

end Rollup.EVM
