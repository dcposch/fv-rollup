import semantics.ActivePrefix
import invariants.Invariants

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- Full in-flight target, including nested calls into the locked rollup itself. -/
def CallbackActivePrefixCorrect : Prop :=
  ∀ (self : Address) (start current : Ethereum.State) (keys : AccessScope) (payment : Payment),
    self ≠ start.executionEnv.codeOwner →
    (start.accountMap.findD self default).code = runtimeBytecode →
    readWord start self ⟨6⟩ ≠ ⟨0⟩ → WorldBounded start →
    Safe (inFlightProjection start self keys payment) → ActivePrefix start current →
    Safe (inFlightProjection current self keys payment)

end Rollup.EVM
