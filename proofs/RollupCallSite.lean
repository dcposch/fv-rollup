import proofs.CallOpcode
import proofs.ExecutionTrace
import Ethereum.Theory.ReturnDataBound

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- A call into the rollup binds the sender and transfers its stated context value. -/
theorem call_opcode_rollup_context {before : Ethereum.State} {cost : Nat}
    {op : Operation} {site : CallSite} {self : Address}
    (foreign : self ≠ before.executionEnv.codeOwner)
    (decoded : CallSite.decode before cost op = some site)
    (receiver : AccountAddress.ofUInt256 site.recipient = self) :
    AccountAddress.ofUInt256 site.source = before.executionEnv.codeOwner ∧
      site.contextValue = site.value := by
  cases op <;> simp only [CallSite.decode] at decoded <;> try contradiction
  all_goals repeat' first | split at decoded | contradiction
  all_goals
    cases Option.some.inj decoded
    first
    | exact ⟨AccountAddress.ofUInt256_ofNat _, rfl⟩
    | exact (foreign (by simpa only [AccountAddress.ofUInt256_ofNat] using receiver.symm)).elim

/-- A child message's calldata is the bounded memory slice selected by the opcode. -/
theorem call_site_calldata_bound (site : CallSite) (before : Ethereum.State) :
    (site.message before).calldata.size < UInt256.size :=
  ByteArray.readWithPadding_size_lt_uint256 _ _ _

/-- The root call's code target and storage context select the same account. -/
theorem call_opcode_rollup_selected {before : Ethereum.State} {cost : Nat}
    {op : Operation} {site : CallSite} {self : Address}
    (foreign : self ≠ before.executionEnv.codeOwner)
    (decoded : CallSite.decode before cost op = some site)
    (receiver : AccountAddress.ofUInt256 site.recipient = self) :
    site.outcome (callParent before) = (site.message (callParent before)).selectedRun := by
  have target := call_opcode_target foreign decoded receiver
  have same : AccountAddress.ofUInt256 site.target = (site.message (callParent before)).receiver :=
    target.trans receiver.symm
  unfold CallSite.outcome MessageCall.selectedRun
  rw [same]
  rfl

/-- The EVM guard and decoded arguments supply the rollup message conditions. -/
theorem call_opcode_rollup_environment {before : Ethereum.State} {cost : Nat}
    {op : Operation} {site : CallSite} {self : Address}
    (foreign : self ≠ before.executionEnv.codeOwner)
    (decoded : CallSite.decode before cost op = some site)
    (receiver : AccountAddress.ofUInt256 site.recipient = self)
    (enabled : site.enabled (callParent before)) :
    MessageEnvironment self (site.message (callParent before)) := by
  have context := call_opcode_rollup_context foreign decoded receiver
  refine ⟨receiver, ?_, context.2, ?_, call_site_calldata_bound _ _⟩
  · change AccountAddress.ofUInt256 site.recipient ≠ AccountAddress.ofUInt256 site.source
    rw [receiver, context.1]
    exact foreign
  · exact call_site_funded site (callParent before) enabled (.inl context.1)

/-- A completed helper call into the rollup has the proved model effects. -/
theorem call_helper_rollup_refines {before after : Ethereum.State} {cost : Nat}
    {op : Operation} {site : CallSite} {self : Address} {keys : AccessScope} {returned : UInt256}
    (ordinary : self ∉ π) (foreign : self ≠ before.executionEnv.codeOwner)
    (decoded : CallSite.decode before cost op = some site)
    (receiver : AccountAddress.ofUInt256 site.recipient = self)
    (enabled : site.enabled (callParent before))
    (ready : BoundaryReady self before.accountMap keys)
    (safe : Safe (boundaryModel self before.accountMap keys))
    (covered : CalldataCovered (site.message (callParent before)).entryState keys)
    (run : site.run (callParent before) = .ok (returned, after)) :
    BoundaryReady self after.accountMap keys ∧ Safe (boundaryModel self after.accountMap keys) ∧
      CallTrace (boundaryModel self before.accountMap keys) (boundaryModel self after.accountMap keys) := by
  rcases outcome : site.outcome (callParent before) with
    ⟨created, accounts, gas, substate, accepted, output⟩
  let result : MessageResult := ⟨created, accounts, gas, substate, accepted, output⟩
  have executed : (site.message (callParent before)).selectedRun = result.tuple := by
    rw [← call_opcode_rollup_selected foreign decoded receiver]
    exact outcome
  have event := ExecutionStep.message (site.message (callParent before)) result
    (call_opcode_rollup_environment foreign decoded receiver enabled) executed
  have refined := execution_step_refines ordinary ready safe event covered
  have accountsSame := call_site_outcome site (callParent before) after returned enabled run
  rw [outcome] at accountsSame
  rw [accountsSame]
  exact ⟨refined.1, refined.2.1, refined.2.2.1⟩

end Rollup.EVM
