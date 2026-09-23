import proofs.generated.LockedPaths
import proofs.support.PathCertificate
import proofs.AbstractCursor

open Ethereum Ethereum.EVM

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Rollup.EVM

/-- The table contains the empty stack at the runtime entry. -/
theorem locked_paths_initial : (⟨⟨0⟩, []⟩ : AbstractCursor) ∈ lockedPaths := by
  decide +kernel

/-- The kernel checks every abstract edge against the pinned runtime bytecode. -/
theorem locked_paths_closed : lockedPaths.all (pathClosedAt runtimeBytecode lockedPaths) = true := by
  decide +kernel

end Rollup.EVM
