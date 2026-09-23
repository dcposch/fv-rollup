import semantics.Environment

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- Inputs to an EVM creation call with zero endowment. -/
structure Deployment where
  blobs : List ByteArray
  created : Batteries.RBSet AccountAddress compare
  genesis : BlockHeader
  blocks : ProcessedBlocks
  accounts : AccountMap
  original : AccountMap
  substate : Substate
  sender : AccountAddress
  origin : AccountAddress
  gas : UInt256
  gasPrice : UInt256
  depth : Fin 1025
  salt : Option ByteArray
  header : BlockHeader

noncomputable def Deployment.address (d : Deployment) (code : ByteArray) : AccountAddress :=
  let nonce := (d.accounts.find? d.sender |>.option ⟨0⟩ (·.nonce)) - ⟨1⟩
  Fin.ofNat _ (fromByteArrayBigEndian ((ffi.KEC (Lambda.L_A d.sender nonce d.salt code)).extract 12 32))

def Deployment.fresh (d : Deployment) (code : ByteArray) : Prop :=
  let old := d.accounts.findD (d.address code) default
  old.nonce = ⟨0⟩ ∧ old.code = ByteArray.empty ∧ old.storage = default

noncomputable def Deployment.initialAccounts (d : Deployment) (code : ByteArray) : AccountMap :=
  let old := d.accounts.findD (d.address code) default
  match d.accounts.find? d.sender with
  | none => d.accounts
  | some sender =>
    (d.accounts.insert d.sender { sender with balance := sender.balance - ⟨0⟩ }).insert
      (d.address code) { old with nonce := old.nonce + ⟨1⟩, balance := ⟨0⟩ + old.balance }

noncomputable def Deployment.initialEnv (d : Deployment) (code : ByteArray) : ExecutionEnv :=
  { codeOwner := d.address code
    sender := d.origin
    source := d.sender
    weiValue := ⟨0⟩
    calldata := default
    code := code
    gasPrice := d.gasPrice.toNat
    header := d.header
    depth := d.depth
    perm := true
    blobVersionedHashes := d.blobs }

noncomputable def Deployment.run (d : Deployment) (code : ByteArray) :=
  Lambda d.blobs d.created d.genesis d.blocks d.accounts d.original d.substate d.sender
    d.origin d.gas d.gasPrice ⟨0⟩ code d.depth d.salt d.header true

noncomputable def Deployment.initialize (d : Deployment) (code : ByteArray) :=
  Ξ (d.created.insert (d.address code)) d.genesis d.blocks (d.initialAccounts code)
    d.original d.gas (d.substate.addAccessedAccount (d.address code)) (d.initialEnv code)

end Rollup.EVM
