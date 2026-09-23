import semantics.TransactionSequence
import semantics.CallEntry

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- The code frame selected by the transaction's message or creation branch. -/
inductive TransactionCodeEntry (event : TransactionEvent) : Ethereum.State → Prop where
  | message {recipient code} (recipientSelected : event.transaction.base.recipient = some recipient)
      (codeSelected : toExecute
        (transactionMessage event.before event.baseFee event.header event.genesis event.blocks
          event.transaction event.sender recipient).accounts recipient = .Code code) :
      TransactionCodeEntry event
        ((transactionMessage event.before event.baseFee event.header event.genesis event.blocks
          event.transaction event.sender recipient).codeEntry code)
  | creation (selected : event.transaction.base.recipient = none) :
      TransactionCodeEntry event
        (transactionCreation event.before event.baseFee event.header event.genesis event.blocks
          event.transaction event.sender).entryState

end Rollup.EVM
