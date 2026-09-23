import proofs.generated.ControlIndexedPaths
import proofs.generated.BlockedCallCertificate
import proofs.generated.ControlCallCertificate
import proofs.support.ControlCallBoundary
import proofs.RuntimeAnyDispatch

open Ethereum Ethereum.EVM

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Rollup.EVM

/-- The checked region remains closed under continuing execution. -/
theorem blocked_control_paths_closed :
    blockedControlPaths.all (controlClosedAt runtimeBytecode blockedControlPaths) = true :=
  indexed_control_closed_sound blocked_control_indexed_closed

/-- This region excludes the withdrawal CALL counter. -/
theorem blocked_control_paths_exclude_call :
    blockedControlPaths.all (fun cursor => cursor.pc != ⟨935⟩) = true :=
  blocked_call_certificate

/-- Every other dispatched function begins in the region with no path to withdrawal CALL. -/
theorem nonwithdraw_entry_blocked (entry : RuntimeEntry) (different : entry ≠ .withdrawal) :
    (⟨runtimeEntryPC entry, [.any]⟩ : AbstractCursor) ∈ blockedControlPaths := by
  cases entry
  all_goals first | exact (different rfl).elim | decide +kernel

/-- A completed runtime CALL enters the region that excludes another withdrawal CALL. -/
theorem control_call_enters_blocked :
    controlPaths.all (controlCallToTable runtimeBytecode blockedControlPaths) = true :=
  control_call_certificate

end Rollup.EVM
