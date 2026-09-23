import proofs.LockedPaths
import proofs.PathCertificate

open Ethereum Ethereum.EVM

set_option maxRecDepth 100000

namespace Rollup.EVM

/-- Every row in the checked table has only successors in that table. -/
theorem locked_paths_row (cursor : AbstractCursor) (member : cursor ∈ lockedPaths) :
    pathClosedAt runtimeBytecode lockedPaths cursor = true := by
  have checked : ∀ index (bounded : index < lockedPaths.size),
      pathClosedAt runtimeBytecode lockedPaths lockedPaths[index] = true := by
    simpa using locked_paths_closed
  obtain ⟨index, bounded, same⟩ := Array.mem_iff_getElem.mp member
  rw [← same]
  exact checked index bounded

/-- A concrete state represented by the table cannot execute an account write or call. -/
theorem locked_cursor_neutral {cursor : AbstractCursor} {state : Ethereum.State}
    (member : cursor ∈ lockedPaths) (code : state.executionEnv.code = runtimeBytecode)
    (represented : cursor.denotes state) :
    AccountPreservingOperation
      ((decode state.executionEnv.code state.machineState.pc).getD (.STOP, none)).1 := by
  rw [code, represented.1]
  exact path_certificate_neutral (locked_paths_row cursor member)

end Rollup.EVM
