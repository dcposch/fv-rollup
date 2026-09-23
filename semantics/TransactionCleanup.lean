import semantics.Boundary

open Ethereum

namespace Rollup.EVM

/-- The final deletion and transient-storage passes in EVMLean's transaction function. -/
def transactionCleanup (accounts : AccountMap) (substate : Substate) : AccountMap :=
  let destroyed := substate.selfDestructSet.1.foldl Batteries.RBMap.erase accounts
  let dead := substate.touchedAccounts.filter (Ethereum.State.dead accounts ·)
  let cleared := dead.foldl Batteries.RBMap.erase destroyed
  cleared.map (fun (owner, account) => (owner, { account with tstorage := ∅ }))

end Rollup.EVM
