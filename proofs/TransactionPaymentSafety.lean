import proofs.TransactionRootEntry
import proofs.RootPaymentSafety

open Ethereum Ethereum.EVM Reasoning.Theory

namespace Rollup.EVM

/-- Custody holds throughout an actual transaction's withdrawal receiver tree. -/
theorem transaction_payment_safe {event start root cursor child current self keys}
    (entry : TransactionCodeEntry event start) (path : CoveredRootEntryPath self keys root start)
    (admissible : event.admissible self) (ordinary : self ∉ π)
    (ready : BoundaryReady self event.before keys) (safe : Safe (boundaryModel self event.before keys))
    (earlier : ContinuingPrefix (D_J runtimeBytecode 0) root cursor)
    (entered : ChildCallEntry (D_J runtimeBytecode 0) cursor child)
    (active : ActivePrefix child current) :
    ∃ owner : Address,
      UInt256.ofNat owner.val = calldataWord root.executionEnv.calldata 4 ∧
      Safe (inFlightProjection current self keys
        ⟨owner, (calldataWord root.executionEnv.calldata 36).toNat,
          (project root self keys).eth⟩) := by
  obtain ⟨fresh, bounded, code, world, storage, solvent, covered⟩ :=
    transaction_root_entry_ready entry path admissible ordinary ready safe
  have result := root_payment_prefix_safe fresh bounded code world storage solvent covered earlier entered active
  have owner := (root_entry_binding path).1
  simpa only [owner] using result

end Rollup.EVM
