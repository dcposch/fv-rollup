import semantics.ExecutionTrace

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- Complete external messages to any receiver. Transaction fees and final deletion are separate. -/
inductive MessageSequence (self : Address) (start : AccountMap) :
    List (MessageCall × MessageResult) → AccountMap → Prop where
  | initial : MessageSequence self start [] start
  | next {events call result}
      (earlier : MessageSequence self start events call.accounts)
      (sender : self ≠ call.sender)
      (context : call.contextValue = call.value)
      (bounded : call.calldata.size < UInt256.size)
      (funds : call.value.toNat ≤ (call.accounts.findD call.sender default).balance.toNat)
      (executed : call.selectedRun = result.tuple) :
      MessageSequence self start (events ++ [(call, result)]) result.accounts

end Rollup.EVM
