import proofs.CreationSite

open Ethereum Ethereum.EVM

set_option maxRecDepth 2048

namespace Rollup.EVM

/-- Both creation opcodes commit the account result of their bound creation call. -/
theorem creation_opcode_accounts {before after : Ethereum.State} {cost : Nat}
    {op : Operation} {arg : Option (UInt256 × Nat)} {site : CreationSite}
    (decoded : CreationSite.decode before op = some site)
    (bounded : (before.accountMap.findD before.executionEnv.codeOwner default).nonce.toNat < 2 ^ 64 - 1)
    (allowed : site.guard before)
    (run : step cost (op, arg) before = .ok after) :
    after.accountMap = (site.call before cost allowed).run.2.2.1 := by
  rcases creation_opcode_kind decoded with rfl | rfl
  all_goals
    simp only [CreationSite.decode] at decoded
    split at decoded <;> try contradiction
    rename_i pop
    cases Option.some.inj decoded
    have below : ¬ ((before.accountMap.find? before.executionEnv.codeOwner).getD default).nonce.toNat ≥
        2 ^ 64 - 1 := Nat.not_le.mpr bounded
    simp only [CreationSite.guard, CreationSite.code] at allowed
    simp only [step, pop] at run
    simp only [below, allowed, if_false, bind, Except.bind] at run
    repeat' first | split at run | contradiction
    all_goals
      have same := Except.ok.inj run
      rw [← same]
      rfl

end Rollup.EVM
