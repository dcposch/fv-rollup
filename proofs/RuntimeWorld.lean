import proofs.SourceWorld
import proofs.RuntimeSource
import proofs.MessageClassification

open Solm Ethereum Ethereum.EVM Reasoning.Theory

namespace Rollup.EVM

/-- Accepted pinned bytecode cannot increase total ETH. Its call label comes from actual calldata. -/
theorem runtime_world_nonincrease {cA gh bl accounts original substate env} {gas : UInt256}
    {created after remaining finalSubstate output} (keys : AccessScope)
    (code : env.code = runtimeBytecode) (bounded : env.calldata.size < UInt256.size)
    (covered : calldataScope env ⊆ keys)
    (own : OwnCode (initState cA gh bl accounts original (.ofUInt256 gas) substate env))
    (world : WorldBounded (initState cA gh bl accounts original (.ofUInt256 gas) substate env))
    (ready : StorageReady (initState cA gh bl accounts original (.ofUInt256 gas) substate env) env.codeOwner keys)
    (run : Ξ cA gh bl accounts original gas substate env =
      .ok (.success (created, after, remaining, finalSubstate) output)) :
    worldEth after ≤ worldEth accounts := by
  obtain ⟨locals, label, bound, scope⟩ := runtime_success_scoped_binding code bounded run
  obtain ⟨frame, sourceOut, values, source, maps, _⟩ :=
    runtime_accepted_source locals label code bounded bound run
  have accesses : entryKeys label.entry ⊆ keys := by
    rw [scope]
    exact covered
  have result := source_world_nonincrease _ sourceOut locals frame label values keys
    bound accesses own world ready source
  rw [world_eth_equiv maps]
  exact result

/-- Complete rollup messages preserve the world budget on success and rollback. -/
theorem rollup_message_world_nonincrease (call : MessageCall) (keys : AccessScope)
    (ready : BoundaryReady call.receiver call.accounts keys) (ordinary : call.receiver ∉ π)
    (different : call.receiver ≠ call.sender) (value : call.contextValue = call.value)
    (funds : call.value.toNat ≤ ethLedger call.accounts call.sender)
    (bounded : call.calldata.size < UInt256.size) (covered : CalldataCovered call.entryState keys)
    {created accounts gas substate accepted output}
    (run : call.selectedRun = (created, accounts, gas, substate, accepted, output)) :
    worldEth accounts ≤ worldEth call.accounts := by
  cases accepted with
  | false =>
    rw [(message_rejected_boundary call keys ready ordinary run).1]
  | true =>
    rw [message_selected_runtime call keys ready ordinary] at run
    have execution := (message_call_accepted call runtimeBytecode created accounts gas substate output run).1
    have initial := message_entry_ready call keys ready different value funds
    have budget := runtime_world_nonincrease keys rfl bounded covered initial.1 initial.2.1
      initial.2.2.1 execution
    have total : worldEth call.initialAccounts = worldEth call.accounts := by
      rw [message_initial_accounts]
      exact sendEth_world call.accounts call.receiver call.sender call.value true funds (BoundaryReady.world ready)
    exact budget.trans total.le

end Rollup.EVM
