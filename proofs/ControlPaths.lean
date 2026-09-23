import proofs.generated.ControlPaths
import proofs.support.ControlCertificate
import proofs.AbstractCursor
import proofs.generated.ControlIndexedPaths
import proofs.generated.ControlChildrenCertificate

open Ethereum Ethereum.EVM

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Rollup.EVM

/-- The candidate table contains the fresh runtime cursor. -/
theorem control_paths_initial : (⟨⟨0⟩, []⟩ : AbstractCursor) ∈ controlPaths := by
  decide +kernel

/-- The kernel checks all candidate edges against the pinned runtime. -/
theorem control_paths_closed : controlPaths.all (controlClosedAt runtimeBytecode controlPaths) = true :=
  indexed_control_closed_sound control_indexed_closed

/-- Every candidate child entry is the withdrawal CALL at byte 935. -/
theorem control_paths_children : controlPaths.all (controlChildAt runtimeBytecode) = true :=
  control_children_certificate

end Rollup.EVM
