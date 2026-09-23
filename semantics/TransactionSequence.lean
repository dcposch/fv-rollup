import semantics.TransactionCalls

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- Inputs and outputs of one complete EVM transaction. -/
structure TransactionEvent where
  before : AccountMap
  after : AccountMap
  baseFee : Nat
  header : BlockHeader
  genesis : BlockHeader
  blocks : ProcessedBlocks
  transaction : Transaction
  sender : Address
  substate : Substate
  accepted : Bool
  gas : UInt256

/-- Execute the event with the pinned EVM transaction semantics. -/
def TransactionEvent.executed (event : TransactionEvent) : Prop :=
  Υ event.before event.baseFee event.header event.genesis event.blocks event.transaction event.sender =
    .ok (event.after, event.substate, event.accepted, event.gas)

/-- Upfront account, nonce, fee, value, and calldata conditions. -/
def TransactionEvent.admissible (event : TransactionEvent) (self : Address) : Prop :=
  self ≠ event.sender ∧
  ∃ account, event.before.find? event.sender = some account ∧
    account.nonce.toNat < 2 ^ 64 - 1 ∧
    event.baseFee ≤ (transactionFeeCap event.transaction).toNat ∧
    event.transaction.base.gasLimit.toNat * (transactionGasPrice event.baseFee event.transaction).toNat +
      calcBlobFee event.header event.transaction + event.transaction.base.value.toNat ≤ account.balance.toNat ∧
    event.transaction.base.data.size < UInt256.size

/-- Storage keys read by all nested frames, including reverted frames. -/
noncomputable def TransactionEvent.scope (event : TransactionEvent) (self : Address) : AccessScope :=
  transactionExecutionScope event.before event.baseFee event.header event.genesis event.blocks
    event.transaction event.sender self

/-- A sequence of actual transactions with their upfront environment conditions. -/
inductive TransactionSequence (self : Address) (start : AccountMap) :
    List TransactionEvent → AccountMap → Prop where
  | initial : TransactionSequence self start [] start
  | next {events event}
      (earlier : TransactionSequence self start events event.before)
      (admissible : event.admissible self) (executed : event.executed) :
      TransactionSequence self start (events ++ [event]) event.after

end Rollup.EVM
