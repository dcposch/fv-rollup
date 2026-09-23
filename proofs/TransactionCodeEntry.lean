import semantics.TransactionCodeEntry
import proofs.TransactionBoundary
import proofs.FreshFrame
import proofs.CreationPrefixBoundary

open Ethereum Ethereum.EVM

set_option maxRecDepth 4096

namespace Rollup.EVM

/-- Upfront fees preserve the boundary and leave the transaction value funded. -/
theorem transaction_checkpoint_boundary {event : TransactionEvent} {self keys}
    (admissible : event.admissible self)
    (ready : BoundaryReady self event.before keys) (safe : Safe (boundaryModel self event.before keys)) :
    let accounts := transactionCheckpoint event.before event.sender event.transaction.base.gasLimit
      (transactionGasPrice event.baseFee event.transaction) (.ofNat (calcBlobFee event.header event.transaction))
    BoundaryRefines self keys event.before accounts ∧
      (accounts.findD event.sender default).nonce ≠ ⟨0⟩ ∧
      event.transaction.base.value.toNat ≤ ethLedger accounts event.sender := by
  obtain ⟨foreign, account, found, nonceBound, priceBound, funded, bounded⟩ := admissible
  have blobBound : calcBlobFee event.header event.transaction < UInt256.size := by
    have bound := account.balance.val.isLt
    change account.balance.toNat < UInt256.size at bound
    omega
  have blobWord := UInt256.toNat_ofNat_of_lt blobBound
  have wordFunds : event.transaction.base.gasLimit.toNat *
      (transactionGasPrice event.baseFee event.transaction).toNat +
      (UInt256.ofNat (calcBlobFee event.header event.transaction)).toNat +
      event.transaction.base.value.toNat ≤ account.balance.toNat := by rwa [blobWord]
  have feeFunds : event.transaction.base.gasLimit.toNat *
      (transactionGasPrice event.baseFee event.transaction).toNat +
      (UInt256.ofNat (calcBlobFee event.header event.transaction)).toNat ≤ account.balance.toNat := by omega
  exact ⟨checkpoint_refines _ _ _ _ _ _ _ _ found foreign feeFunds ready safe,
    checkpoint_nonce_nonzero _ _ _ _ _ _ found nonceBound,
    checkpoint_value_funded _ _ _ _ _ _ _ found wordFunds⟩

/-- Transaction code execution starts with a fresh frame. -/
theorem transaction_code_entry_fresh {event start} (entry : TransactionCodeEntry event start) :
    FreshFrame start := by
  cases entry <;> rfl

/-- Admissible transactions and creation use word-bounded calldata. -/
theorem transaction_code_entry_bounded {event start self} (entry : TransactionCodeEntry event start)
    (admissible : event.admissible self) : start.executionEnv.calldata.size < UInt256.size := by
  cases entry with
  | message recipientSelected codeSelected =>
    obtain ⟨_, account, _, _, _, _, bounded⟩ := admissible
    exact bounded
  | creation selected =>
    change ByteArray.empty.size < UInt256.size
    decide +kernel

/-- Entry preserves the rollup boundary, except for an invalid creation collision stub. -/
theorem transaction_code_entry_boundary {event start self keys}
    (entry : TransactionCodeEntry event start) (admissible : event.admissible self)
    (ready : BoundaryReady self event.before keys) (safe : Safe (boundaryModel self event.before keys)) :
    (start.executionEnv.code = ⟨#[0xfe]⟩ ∧ start.machineState.pc = ⟨0⟩) ∨
      BoundaryRefines self keys event.before start.accountMap := by
  have checkpoint := transaction_checkpoint_boundary admissible ready safe
  cases entry with
  | @message recipient code recipientSelected codeSelected =>
    apply Or.inr
    let call := transactionMessage event.before event.baseFee event.header event.genesis event.blocks
      event.transaction event.sender recipient
    have transfer := boundary_transfer_refines self call.sender call.receiver call.accounts call.value keys
      checkpoint.1.1 checkpoint.1.2.1 (Or.inl admissible.1) checkpoint.2.2
    exact boundary_refines_trans checkpoint.1 transfer
  | creation selected =>
    let call := transactionCreation event.before event.baseFee event.header event.genesis event.blocks
      event.transaction event.sender
    cases collision : call.collision with
    | true =>
      apply Or.inl
      refine ⟨?_, rfl⟩
      change (if call.collision then (⟨#[0xfe]⟩ : ByteArray) else call.initCode) = _
      rw [collision]
      rfl
    | false =>
      apply Or.inr
      have different := creation_fresh_not_sender call checkpoint.2.1 collision
      have transfer := boundary_creation_transfer_refines self call.sender call.address call.accounts call.value keys
        checkpoint.1.1 checkpoint.1.2.1 admissible.1 different checkpoint.2.2
      exact boundary_refines_trans checkpoint.1 transfer

end Rollup.EVM
