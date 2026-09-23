import semantics.Payments
import semantics.Environment

namespace Rollup.EVM

/-- A successful source call has this storage state and labeled effect. -/
def SourceResult (evm out : Ethereum.State) (locals : Solm.Store) (frame : Solm.Frame)
    (call : Call) (values : Option (List Solm.Value)) (keys : AccessScope) : Prop :=
  StorageReady out evm.executionEnv.codeOwner keys ∧
  readWord out evm.executionEnv.codeOwner ⟨6⟩ = ⟨0⟩ ∧
  out.executionEnv = evm.executionEnv ∧
  OwnCode out ∧ WorldBounded out ∧
  ∃ result payments, values = returnValues result ∧
    CallStep (beforeCall evm keys) call (.success result) payments
      (project out evm.executionEnv.codeOwner keys) ∧
    PaymentBound evm out locals frame call.entry

end Rollup.EVM
