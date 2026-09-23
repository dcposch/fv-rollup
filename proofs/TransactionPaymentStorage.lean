import proofs.FreshPaymentPrefix
import proofs.TransactionRootEntry

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- Callbacks in actual transactions preserve the locked rollup's code and storage. -/
theorem transaction_payment_storage {event start root cursor child current self keys}
    (entry : TransactionCodeEntry event start) (path : CoveredRootEntryPath self keys root start)
    (admissible : event.admissible self) (ordinary : self ∉ π)
    (ready : BoundaryReady self event.before keys) (safe : Safe (boundaryModel self event.before keys))
    (earlier : ContinuingPrefix (D_J runtimeBytecode 0) root cursor)
    (entered : ChildCallEntry (D_J runtimeBytecode 0) cursor child) (active : ActivePrefix child current) :
    CodeStorageFrame self (withdrawalLockedState root).accountMap current.accountMap := by
  obtain ⟨fresh, bounded, code, world, storage, solvent, covered⟩ :=
    transaction_root_entry_ready entry path admissible ordinary ready safe
  have frame := fresh_root_payment_storage fresh bounded code world storage solvent covered earlier entered active
  simpa only [(root_entry_binding path).1] using frame

end Rollup.EVM
