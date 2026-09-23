import semantics.Boundary

open Ethereum

namespace Rollup.EVM

/-- Debit prepaid execution and blob fees, then increment the sender nonce. -/
def transactionCheckpoint (accounts : AccountMap) (sender : Address)
    (gasLimit price blobFee : UInt256) : AccountMap :=
  let account := (accounts.find? sender).get!
  accounts.insert sender { account with
    balance := account.balance - gasLimit * price - blobFee
    nonce := account.nonce + ⟨1⟩ }

/-- Return unused gas payment and credit the block beneficiary. -/
def transactionFeeCredits (accounts : AccountMap) (sender beneficiary : Address)
    (refund fee : UInt256) : AccountMap :=
  let refunded := accounts.increaseBalance sender refund
  if fee != UInt256.ofNat 0 then refunded.increaseBalance beneficiary fee else refunded

end Rollup.EVM
