import semantics.ChildCall
import semantics.ChildCreation
import Reasoning.Stepping

open Ethereum Ethereum.EVM Reasoning.Theory

namespace Rollup.EVM

/-- A code frame starts with the exact fresh state used by the EVM interpreter. -/
def FreshFrame (state : Ethereum.State) : Prop :=
  state = initState state.createdAccounts state.genesisBlockHeader state.blocks state.accountMap state.σ₀
    state.machineState.gasAvailable state.substate state.executionEnv

end Rollup.EVM
