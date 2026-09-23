import semantics.Environment

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- Inputs to an EVM message call. Transfer value and context value can differ. -/
structure MessageCall where
  blobs : List ByteArray
  created : Batteries.RBSet AccountAddress compare
  genesis : BlockHeader
  blocks : ProcessedBlocks
  accounts : AccountMap
  original : AccountMap
  substate : Substate
  sender : AccountAddress
  origin : AccountAddress
  receiver : AccountAddress
  gas : UInt256
  gasPrice : UInt256
  value : UInt256
  contextValue : UInt256
  calldata : ByteArray
  depth : Fin 1025
  header : BlockHeader
  writable : Bool

/-- The call credits the receiver before it debits the sender. -/
noncomputable def MessageCall.initialAccounts (c : MessageCall) : AccountMap :=
  let credited := match c.accounts.find? c.receiver with
    | none => if c.value != UInt256.ofNat 0 then
        c.accounts.insert c.receiver { (default : Account) with balance := c.value }
      else c.accounts
    | some account => c.accounts.insert c.receiver
        { account with balance := account.balance + c.value }
  match credited.find? c.sender with
    | none => credited
    | some account => credited.insert c.sender
        { account with balance := account.balance - c.value }

noncomputable def MessageCall.environment (c : MessageCall) (code : ByteArray) : ExecutionEnv :=
  { codeOwner := c.receiver
    sender := c.origin
    source := c.sender
    weiValue := c.contextValue
    calldata := c.calldata
    code := code
    gasPrice := c.gasPrice.toNat
    header := c.header
    depth := c.depth
    perm := c.writable
    blobVersionedHashes := c.blobs }

noncomputable def MessageCall.execute (c : MessageCall) (code : ByteArray) :=
  Ξ c.created c.genesis c.blocks c.initialAccounts c.original c.gas c.substate
    (c.environment code)

noncomputable def MessageCall.run (c : MessageCall) (code : ByteArray) :=
  Θ c.blobs c.created c.genesis c.blocks c.accounts c.original c.substate c.sender
    c.origin c.receiver (.Code code) c.gas c.gasPrice c.value c.contextValue c.calldata
    c.depth c.header c.writable

end Rollup.EVM
