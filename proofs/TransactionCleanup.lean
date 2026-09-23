import semantics.TransactionCleanup
import proofs.DeadAccounts
import proofs.TransientReset

open Ethereum

namespace Rollup.EVM

/-- Final cleanup preserves the rollup once its absence from pending deletions is established. -/
theorem transaction_cleanup_refines (self : Address) (accounts : AccountMap) (substate : Substate)
    (keys : AccessScope) (absent : self ∉ substate.selfDestructSet)
    (ready : BoundaryReady self accounts keys) (safe : Safe (boundaryModel self accounts keys)) :
    BoundaryRefines self keys accounts (transactionCleanup accounts substate) := by
  have deletions := transaction_deletions_refine self accounts substate keys absent ready safe
  have reset := reset_transient_refines _ self keys deletions.1 deletions.2.1
  exact boundary_refines_trans deletions reset

end Rollup.EVM
