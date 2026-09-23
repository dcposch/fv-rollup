import proofs.CreationLifecycle

open Ethereum Ethereum.EVM

set_option maxRecDepth 2048
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

namespace Rollup.EVM

/-- A successful creation opcode either preserves lifecycle fields or executes its checked creation call. -/
theorem creation_opcode_lifecycle_cases {before after : Ethereum.State} {cost : Nat}
    {op : Operation} {arg : Option (UInt256 × Nat)}
    (kind : op = .CREATE ∨ op = .CREATE2)
    (run : step cost (op, arg) before = .ok after) :
    (after.accountMap = before.accountMap ∧ after.createdAccounts = before.createdAccounts ∧
      after.substate = before.substate) ∨
      ∃ site, CreationSite.decode before op = some site ∧
        (before.accountMap.findD before.executionEnv.codeOwner default).nonce.toNat < 2 ^ 64 - 1 ∧
        ∃ allowed : site.guard before,
          after.accountMap = (site.call before cost allowed).run.2.2.1 ∧
          after.createdAccounts = (site.call before cost allowed).run.2.1 ∧
          after.substate = (site.call before cost allowed).run.2.2.2.2.1 := by
  rcases kind with rfl | rfl
  all_goals
    by_cases bounded : (before.accountMap.findD before.executionEnv.codeOwner default).nonce.toNat < 2 ^ 64 - 1
    · cases decoded : CreationSite.decode before _ with
      | none =>
        simp only [CreationSite.decode] at decoded
        split at decoded <;> try contradiction
        rename_i pop
        simp only [step, pop] at run
        contradiction
      | some site =>
        by_cases allowed : site.guard before
        · exact .inr ⟨site, rfl, bounded, allowed, creation_opcode_lifecycle decoded bounded allowed run⟩
        · apply Or.inl
          simp only [CreationSite.decode] at decoded
          split at decoded <;> try contradiction
          rename_i pop
          cases Option.some.inj decoded
          have below := Nat.not_le.mpr bounded
          simp only [CreationSite.guard, CreationSite.code] at allowed
          simp only [step, pop, below, allowed, if_false, bind, Except.bind] at run
          repeat' first | split at run | contradiction
          all_goals
            have same := Except.ok.inj run
            rw [← same]
            exact ⟨rfl, rfl, rfl⟩
    · apply Or.inl
      have full := Nat.le_of_not_gt bounded
      simp only [step] at run
      split at run <;> try contradiction
      simp only [full, if_true, bind, Except.bind] at run
      repeat' first | split at run | contradiction
      all_goals
        have same := Except.ok.inj run
        rw [← same]
        exact ⟨rfl, rfl, rfl⟩

end Rollup.EVM
