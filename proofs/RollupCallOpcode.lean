import proofs.RollupCallSite

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- Decoding a helper site identifies one of the four call opcodes. -/
theorem call_opcode_kind {before : Ethereum.State} {cost : Nat} {op : Operation} {site : CallSite}
    (decoded : CallSite.decode before cost op = some site) :
    op = .CALL ∨ op = .CALLCODE ∨ op = .DELEGATECALL ∨ op = .STATICCALL := by
  cases op <;> rename_i command <;> cases command <;> simp_all [CallSite.decode]

/-- Failure of the funds or depth guard leaves accounts unchanged. -/
theorem call_site_disabled_accounts (site : CallSite) (before after : Ethereum.State) (result : UInt256)
    (disabled : ¬ site.enabled before) (run : site.run before = .ok (result, after)) :
    after.accountMap = before.accountMap := by
  have blocked : ¬ (site.value ≤ (before.accountMap.find? before.executionEnv.codeOwner).option
    ⟨0⟩ (·.balance) ∧ before.executionEnv.depth < 1024) := disabled
  unfold CallSite.run call at run
  simp only [blocked, if_false] at run
  have same := congrArg Prod.snd (Except.ok.inj run)
  exact (congrArg Ethereum.State.accountMap same).symm

/-- The helper either enters the proved rollup message or leaves accounts unchanged. -/
theorem call_helper_rollup_total {before after : Ethereum.State} {cost : Nat}
    {op : Operation} {site : CallSite} {self : Address} {keys : AccessScope} {returned : UInt256}
    (ordinary : self ∉ π) (foreign : self ≠ before.executionEnv.codeOwner)
    (decoded : CallSite.decode before cost op = some site)
    (receiver : AccountAddress.ofUInt256 site.recipient = self)
    (ready : BoundaryReady self before.accountMap keys)
    (safe : Safe (boundaryModel self before.accountMap keys))
    (covered : CalldataCovered (site.message (callParent before)).entryState keys)
    (run : site.run (callParent before) = .ok (returned, after)) :
    BoundaryReady self after.accountMap keys ∧ Safe (boundaryModel self after.accountMap keys) ∧
      CallTrace (boundaryModel self before.accountMap keys) (boundaryModel self after.accountMap keys) := by
  by_cases enabled : site.enabled (callParent before)
  · exact call_helper_rollup_refines ordinary foreign decoded receiver enabled ready safe covered run
  · have accounts := call_site_disabled_accounts site (callParent before) after returned enabled run
    change after.accountMap = before.accountMap at accounts
    rw [accounts]
    exact ⟨ready, safe, .initial⟩

/-- An actual call opcode into the rollup refines the complete model trace. -/
theorem call_opcode_rollup_refines {before after : Ethereum.State} {cost : Nat}
    {op : Operation} {arg : Option (UInt256 × Nat)} {site : CallSite}
    {self : Address} {keys : AccessScope}
    (ordinary : self ∉ π) (foreign : self ≠ before.executionEnv.codeOwner)
    (decoded : CallSite.decode before cost op = some site)
    (receiver : AccountAddress.ofUInt256 site.recipient = self)
    (ready : BoundaryReady self before.accountMap keys)
    (safe : Safe (boundaryModel self before.accountMap keys))
    (covered : CalldataCovered (site.message (callParent before)).entryState keys)
    (run : step cost (op, arg) before = .ok after) :
    BoundaryReady self after.accountMap keys ∧ Safe (boundaryModel self after.accountMap keys) ∧
      CallTrace (boundaryModel self before.accountMap keys) (boundaryModel self after.accountMap keys) := by
  obtain ⟨actual, arguments, returned, during, helper, accounts⟩ :=
    call_opcode_helper (call_opcode_kind decoded) run
  have same : actual = site := Option.some.inj (arguments.symm.trans decoded)
  subst actual
  have result := call_helper_rollup_total ordinary foreign decoded receiver ready safe covered helper
  simpa only [accounts] using result

end Rollup.EVM
