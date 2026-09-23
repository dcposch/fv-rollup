import semantics.ExecutionTree

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- An existing rollup keeps its code and is absent from both transaction lifecycle sets. -/
structure AccountSurvives (self : Address) (accounts : AccountMap)
    (created : Batteries.RBSet AccountAddress compare) (substate : Substate) : Prop where
  pinned : (accounts.findD self default).code = runtimeBytecode
  notCreated : self ∉ created
  notDeleted : self ∉ substate.selfDestructSet

/-- The account-survival condition at an instruction boundary. -/
def StateSurvives (self : Address) (state : Ethereum.State) : Prop :=
  AccountSurvives self state.accountMap state.createdAccounts state.substate

/-- A successful frame preserves the existing account. Callers roll back other outcomes. -/
def FrameResultSurvives (self : Address) :
    Except ExecutionException (ExecutionResult Ethereum.State) → Prop
  | .ok (.success after _) => StateSurvives self after
  | .ok (.revert _ _) => True
  | .error _ => True

end Rollup.EVM
