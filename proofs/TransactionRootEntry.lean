import proofs.TransactionCodeEntry
import proofs.RootEntryBoundary

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- An actual transaction path preserves the boundary up to its root invocation. -/
theorem transaction_root_entry_boundary {event start root self keys}
    (entry : TransactionCodeEntry event start) (path : CoveredRootEntryPath self keys root start)
    (admissible : event.admissible self) (ordinary : self ∉ π)
    (ready : BoundaryReady self event.before keys) (safe : Safe (boundaryModel self event.before keys)) :
    BoundaryRefines self keys event.before root.accountMap := by
  rcases transaction_code_entry_boundary entry admissible ready safe with ⟨invalid, zero⟩ | first
  · exact False.elim (root_entry_invalid (covered_root_entry_execution path) invalid zero)
  · exact boundary_refines_trans first (root_entry_boundary path ordinary first.1 first.2.1)

/-- Root invocation conditions follow from the actual transaction and foreign frame path. -/
theorem transaction_root_entry_ready {event start root self keys}
    (entry : TransactionCodeEntry event start) (path : CoveredRootEntryPath self keys root start)
    (admissible : event.admissible self) (ordinary : self ∉ π)
    (ready : BoundaryReady self event.before keys) (safe : Safe (boundaryModel self event.before keys)) :
    FreshFrame root ∧ root.executionEnv.calldata.size < UInt256.size ∧
      OwnCode root ∧ WorldBounded root ∧ StorageReady root root.executionEnv.codeOwner keys ∧
      Safe (project root root.executionEnv.codeOwner keys) ∧ CalldataCovered root keys := by
  have actual := covered_root_entry_execution path
  refine ⟨root_entry_fresh actual (transaction_code_entry_fresh entry),
    root_entry_bounded actual (transaction_code_entry_bounded entry admissible), ?_⟩
  rcases transaction_code_entry_boundary entry admissible ready safe with ⟨invalid, zero⟩ | first
  · exact False.elim (root_entry_invalid actual invalid zero)
  · exact root_entry_ready path ordinary first.1 first.2.1

end Rollup.EVM
