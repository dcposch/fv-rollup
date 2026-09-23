import proofs.RuntimeWorld
import proofs.RollupCallSite

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- A decoded call helper into the rollup preserves total ETH. -/
theorem call_helper_rollup_budget {before after : Ethereum.State} {cost : Nat}
    {op : Operation} {site : CallSite} {self : Address} {keys : AccessScope} {returned : UInt256}
    (ordinary : self ∉ π) (foreign : self ≠ before.executionEnv.codeOwner)
    (decoded : CallSite.decode before cost op = some site)
    (receiver : AccountAddress.ofUInt256 site.recipient = self)
    (enabled : site.enabled (callParent before))
    (ready : BoundaryReady self before.accountMap keys)
    (covered : CalldataCovered (site.message (callParent before)).entryState keys)
    (run : site.run (callParent before) = .ok (returned, after)) :
    worldEth after.accountMap ≤ worldEth before.accountMap := by
  rcases outcome : site.outcome (callParent before) with
    ⟨created, accounts, gas, substate, accepted, output⟩
  have executed : (site.message (callParent before)).selectedRun =
      (created, accounts, gas, substate, accepted, output) := by
    rw [← call_opcode_rollup_selected foreign decoded receiver]
    exact outcome
  have environment := call_opcode_rollup_environment foreign decoded receiver enabled
  have rootReady : BoundaryReady (site.message (callParent before)).receiver
      (site.message (callParent before)).accounts keys := by
    change BoundaryReady (AccountAddress.ofUInt256 site.recipient) before.accountMap keys
    rwa [receiver]
  have rootOrdinary : (site.message (callParent before)).receiver ∉ π := by
    change AccountAddress.ofUInt256 site.recipient ∉ π
    rwa [receiver]
  have budget := rollup_message_world_nonincrease (site.message (callParent before)) keys
    rootReady rootOrdinary environment.2.1 environment.2.2.1 environment.2.2.2.1
    environment.2.2.2.2 covered executed
  have accountsSame := call_site_outcome site (callParent before) after returned enabled run
  rw [outcome] at accountsSame
  rw [accountsSame]
  exact budget

end Rollup.EVM
