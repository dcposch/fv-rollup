import proofs.DepositRefinement
import proofs.BatchRefinement
import proofs.GetterRefinement
import proofs.WithdrawalRefinement

namespace Rollup.EVM

/-- Every accepted source entry implements its labeled model effect. -/
theorem source_refines_model : SourceRefinesModel := by
  intro evm out locals frame call values keys bound accesses code world ready unlocked funds safe run
  rcases call with ⟨caller, value, entry⟩
  cases entry with
  | deposit owner =>
    exact deposit_source_refines evm out locals frame caller owner value values keys
      bound accesses code world ready funds run
  | executeBatch batch =>
    exact batch_source_refines evm out locals frame caller value batch values keys
      bound accesses code world ready run
  | withdrawPendingBalance owner amount =>
    exact withdrawal_source_refines evm out locals frame caller owner value amount values keys
      bound accesses code world ready safe run
  | read getter =>
    exact getter_source_refines evm out locals frame caller value getter values keys
      bound accesses code world ready unlocked run

end Rollup.EVM
