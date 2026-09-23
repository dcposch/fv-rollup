import proofs.SurvivalMessage
import proofs.SurvivalPrecompile
import proofs.CallOpcode

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- A call helper adds access metadata without changing account survival at entry. -/
theorem call_site_initial_survives (site : CallSite) (before : Ethereum.State) {self : Address}
    (initial : StateSurvives self before) :
    AccountSurvives self (site.message before).accounts (site.message before).created (site.message before).substate := by
  refine ⟨AccountSurvives.pinned initial, AccountSurvives.notCreated initial, ?_⟩
  change self ∉ before.substate.selfDestructSet
  exact AccountSurvives.notDeleted initial

/-- The call helper commits the lifecycle fields returned by its selected message. -/
theorem call_site_survival_result (site : CallSite) (before after : Ethereum.State)
    {self : Address} {returned : UInt256}
    (enabled : site.enabled before)
    (survived : AccountSurvives self (site.outcome before).2.1 (site.outcome before).1
      (site.outcome before).2.2.2.1)
    (run : site.run before = .ok (returned, after)) : StateSurvives self after := by
  unfold CallSite.run call at run
  simp only [enabled.1, enabled.2, and_self, if_true] at run
  have same := congrArg Prod.snd (Except.ok.inj run)
  dsimp only at same
  rw [← same]
  exact survived

/-- A disabled call preserves code and both lifecycle sets. -/
theorem call_site_disabled_survives (site : CallSite) (before after : Ethereum.State)
    {self : Address} {returned : UInt256} (initial : StateSurvives self before)
    (disabled : ¬ site.enabled before) (run : site.run before = .ok (returned, after)) :
    StateSurvives self after := by
  have blocked : ¬ (site.value ≤ (before.accountMap.find? before.executionEnv.codeOwner).option
    ⟨0⟩ (·.balance) ∧ before.executionEnv.depth < 1024) := disabled
  unfold CallSite.run call at run
  simp only [blocked, if_false] at run
  have same := congrArg Prod.snd (Except.ok.inj run)
  dsimp only at same
  rw [← same]
  refine ⟨AccountSurvives.pinned initial, AccountSurvives.notCreated initial, ?_⟩
  change self ∉ before.substate.selfDestructSet
  exact AccountSurvives.notDeleted initial

/-- Complete call helpers preserve account survival through code, precompiles, and failed guards. -/
theorem call_site_survives (site : CallSite) (before after : Ethereum.State)
    {self : Address} {returned : UInt256} (initial : StateSurvives self before)
    (frames : ∀ code, site.enabled before →
      toExecute before.accountMap (AccountAddress.ofUInt256 site.target) = .Code code →
      FrameResultSurvives self
        (X (((site.message before).codeEntry code).machineState.gasAvailable.toNat + 1)
          (D_J code 0) ((site.message before).codeEntry code)))
    (run : site.run before = .ok (returned, after)) : StateSurvives self after := by
  by_cases enabled : site.enabled before
  · apply call_site_survival_result site before after enabled (run := run)
    have entry := call_site_initial_survives site before initial
    rcases executed : site.outcome before with ⟨created, accounts, gas, substate, accepted, output⟩
    cases selected : toExecute before.accountMap (AccountAddress.ofUInt256 site.target) with
    | Code code =>
      rw [call_site_code site before code selected] at executed
      exact message_execution_survives (site.message before) code entry (frames code enabled selected) executed
    | Precompiled pc =>
      unfold CallSite.outcome at executed
      rw [selected] at executed
      exact precompiled_call_survives entry executed
  · exact call_site_disabled_survives site before after initial enabled run

/-- The opcode keeps the accounts and lifecycle metadata returned by its call helper. -/
theorem call_opcode_lifecycle {before after : Ethereum.State} {cost : Nat}
    {op : Operation} {arg : Option (UInt256 × Nat)}
    (kind : op = .CALL ∨ op = .CALLCODE ∨ op = .DELEGATECALL ∨ op = .STATICCALL)
    (run : step cost (op, arg) before = .ok after) :
    ∃ site, CallSite.decode before cost op = some site ∧
      ∃ result during, site.run (callParent before) = .ok (result, during) ∧
        after.accountMap = during.accountMap ∧ after.createdAccounts = during.createdAccounts ∧
        after.substate = during.substate := by
  rcases kind with rfl | rfl | rfl | rfl
  all_goals
    simp [step, bind, Except.bind] at run
    split at run <;> try contradiction
    rename_i popped pop
    split at run <;> try contradiction
    rename_i outcome execute
    rcases outcome with ⟨result, during⟩
    have same := Except.ok.inj run
    rw [← same]
    simp only [CallSite.decode, option_liftM_eq_some pop]
    exact ⟨_, rfl, result, during, execute, rfl, rfl, rfl⟩

end Rollup.EVM
