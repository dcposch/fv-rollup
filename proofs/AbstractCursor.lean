import proofs.support.AbstractCursor
import proofs.AccountOperations
import proofs.PrecheckCursor

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- Each supported abstract instruction preserves accounts in the EVM model. -/
theorem abstract_successors_neutral {cursor : AbstractCursor} {op : Operation}
    {arg : Option (UInt256 × Nat)} {next : List AbstractCursor}
    (supported : cursor.successors op arg = some next) : AccountPreservingOperation op := by
  cases op <;> rename_i command <;> cases command <;>
    simp_all [AbstractCursor.successors, AccountPreservingOperation]

/-- Gas and instruction checks leave an abstract cursor valid. -/
theorem abstract_cursor_precheck {cursor : AbstractCursor} {before after : Ethereum.State}
    {jumps : Array UInt256} {op : Operation} {cost : Nat}
    (represented : cursor.denotes before) (run : Z jumps op before = .ok (after, cost)) :
    cursor.denotes after := by
  have fixed := precheck_cursor run
  simpa only [AbstractCursor.denotes, fixed.1, fixed.2] using represented

end Rollup.EVM
