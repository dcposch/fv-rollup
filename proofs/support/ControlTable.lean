import proofs.support.ControlCertificate
import semantics.ExecutionPrefix

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- A concrete frame cursor represented in a supplied control table. -/
def ControlTableReady (code : ByteArray) (table : Array AbstractCursor) (state : Ethereum.State) : Prop :=
  state.executionEnv.code = code ∧ ∃ cursor ∈ table, cursor.denotes state

end Rollup.EVM
