import proofs.support.AccountOperations
import semantics.ActivePrefix

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- A frame invariant that excludes account writes and child execution. -/
structure AccountFrameCertificate (jumps : Array UInt256) where
  accepts : Ethereum.State → Prop
  operation : ∀ state, accepts state →
    AccountPreservingOperation
      ((decode state.executionEnv.code state.machineState.pc).getD (.STOP, none)).1
  continues : ∀ before after, accepts before → Xstep jumps before = .ok (after, none) →
    accepts { after with executionEnv.depth := before.executionEnv.depth }

end Rollup.EVM
