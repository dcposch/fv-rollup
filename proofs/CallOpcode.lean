import semantics.CallOpcode
import proofs.CallEntry

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- Each completed call opcode has the decoded helper execution and its account result. -/
theorem call_opcode_helper {before after : Ethereum.State} {cost : Nat}
    {op : Operation} {arg : Option (UInt256 × Nat)}
    (kind : op = .CALL ∨ op = .CALLCODE ∨ op = .DELEGATECALL ∨ op = .STATICCALL)
    (run : step cost (op, arg) before = .ok after) :
    ∃ site, CallSite.decode before cost op = some site ∧
      ∃ result during, site.run (callParent before) = .ok (result, during) ∧
        after.accountMap = during.accountMap := by
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
    exact ⟨_, rfl, result, during, execute, rfl⟩

/-- Decoded call arguments debit the current account, or transfer zero ETH. -/
theorem call_opcode_source {before : Ethereum.State} {cost : Nat} {op : Operation} {site : CallSite}
    (decoded : CallSite.decode before cost op = some site) :
    AccountAddress.ofUInt256 site.source = before.executionEnv.codeOwner ∨ site.value = ⟨0⟩ := by
  cases op <;> simp only [CallSite.decode] at decoded <;> try contradiction
  all_goals
    repeat' first | split at decoded | contradiction
  all_goals
    cases Option.some.inj decoded
    simp [AccountAddress.ofUInt256_ofNat]

/-- A foreign caller can enter the protected storage context only through its selected code. -/
theorem call_opcode_target {before : Ethereum.State} {cost : Nat} {op : Operation} {site : CallSite}
    {self : Address} (foreign : self ≠ before.executionEnv.codeOwner)
    (decoded : CallSite.decode before cost op = some site)
    (receiver : AccountAddress.ofUInt256 site.recipient = self) :
    AccountAddress.ofUInt256 site.target = self := by
  cases op <;> simp only [CallSite.decode] at decoded <;> try contradiction
  all_goals
    repeat' first | split at decoded | contradiction
  all_goals
    cases Option.some.inj decoded
    first
    | exact receiver
    | exact (foreign (by simpa only [AccountAddress.ofUInt256_ofNat] using receiver.symm)).elim

/-- Decoded call opcodes preserve the reservation inside a foreign child frame. -/
theorem call_opcode_prefix_safe {before current : Ethereum.State} {cost : Nat}
    {op : Operation} {site : CallSite} {self : Address}
    (keys : AccessScope) (payment : Payment) (code : ByteArray)
    (decoded : CallSite.decode before cost op = some site)
    (enabled : site.enabled (callParent before))
    (foreign : self ≠ before.executionEnv.codeOwner)
    (receiver : self ≠ AccountAddress.ofUInt256 site.recipient)
    (initial : LockedWorld self before.accountMap)
    (safe : Safe (inFlightProjection before self keys payment))
    (trace : InstructionPrefix (D_J code 0)
      ((site.message (callParent before)).codeEntry code) current) :
    LockedWorld self current.accountMap ∧ Safe (inFlightProjection current self keys payment) := by
  exact call_site_prefix_safe site (callParent before) current self keys payment code enabled
    (call_opcode_source decoded) foreign receiver initial safe trace

end Rollup.EVM
