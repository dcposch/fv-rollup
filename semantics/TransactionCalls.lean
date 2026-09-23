import semantics.TransactionExecution
import semantics.ExecutionScope

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- The message selected by a transaction with a recipient. -/
noncomputable def transactionMessage (accounts : AccountMap) (baseFee : Nat)
    (header genesis : BlockHeader) (blocks : ProcessedBlocks) (tx : Transaction)
    (sender recipient : Address) : MessageCall :=
  let price := transactionGasPrice baseFee tx
  let checkpoint := transactionCheckpoint accounts sender tx.base.gasLimit price (.ofNat (calcBlobFee header tx))
  { blobs := tx.blobVersionedHashes
    created := .empty
    genesis := genesis
    blocks := blocks
    accounts := checkpoint
    original := checkpoint
    substate := transactionInitialSubstate header tx sender
    sender := sender
    origin := sender
    receiver := recipient
    gas := .ofNat (tx.base.gasLimit.toNat - intrinsicGas tx)
    gasPrice := price
    value := tx.base.value
    contextValue := tx.base.value
    calldata := tx.base.data
    depth := 0
    header := header
    writable := true }

/-- The creation selected by a transaction without a recipient. -/
noncomputable def transactionCreation (accounts : AccountMap) (baseFee : Nat)
    (header genesis : BlockHeader) (blocks : ProcessedBlocks) (tx : Transaction) (sender : Address) : CreationCall :=
  let price := transactionGasPrice baseFee tx
  let checkpoint := transactionCheckpoint accounts sender tx.base.gasLimit price (.ofNat (calcBlobFee header tx))
  { blobs := tx.blobVersionedHashes
    created := .empty
    genesis := genesis
    blocks := blocks
    accounts := checkpoint
    original := checkpoint
    substate := transactionInitialSubstate header tx sender
    sender := sender
    origin := sender
    gas := .ofNat (tx.base.gasLimit.toNat - intrinsicGas tx)
    gasPrice := price
    value := tx.base.value
    initCode := tx.base.data
    depth := 0
    salt := none
    header := header
    writable := true }

/-- Collect all rollup calldata keys from the selected transaction execution. -/
noncomputable def transactionExecutionScope (accounts : AccountMap) (baseFee : Nat)
    (header genesis : BlockHeader) (blocks : ProcessedBlocks) (tx : Transaction) (sender self : Address) : AccessScope :=
  match tx.base.recipient with
  | none => creationExecutionScope (transactionCreation accounts baseFee header genesis blocks tx sender) self
  | some recipient => selectedMessageScope (transactionMessage accounts baseFee header genesis blocks tx sender recipient) self

/-- The maximum execution-gas price carried by the transaction. -/
def transactionFeeCap (tx : Transaction) : UInt256 :=
  match tx with
  | .legacy data | .access data => data.gasPrice
  | .dynamic data | .blob data => data.maxFeePerGas

end Rollup.EVM
