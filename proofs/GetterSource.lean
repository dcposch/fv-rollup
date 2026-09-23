import semantics.Bindings
import proofs.SourceSteps

open Solm

namespace Rollup.EVM

private theorem require_return_preserves_state
    {cfg frame evm guard expressions outFrame out values}
    (run : ExecFuncBody cfg frame evm [.require guard, .return expressions]
      (.returned outFrame out values)) : out = evm ∧ outFrame = frame := by
  cases run <;>
    repeat' first | cases_type ExecBlock | cases_type ExecStmt
  exact ⟨rfl, rfl⟩

/-- Every accepted source getter preserves the EVM state and local frame. -/
theorem getter_source_preserves_state (getter : Getter)
    (evm out : Ethereum.State) (locals : Store) (frame : Frame)
    (values : Option (List Value))
    (run : ExecTransitionBody config contract evm locals
      (entryTransition (.read getter)).body (.returned frame out values)) :
    out = evm ∧ frame = ⟨contract, locals⟩ := by
  cases getter <;> exact require_return_preserves_state run

end Rollup.EVM
