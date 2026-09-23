import proofs.WorldSelfdestruct
import proofs.CallbackFrame

open Ethereum Ethereum.EVM

namespace Rollup.EVM

private theorem balance_insert_static (accounts : AccountMap) (owner : Address) (balance : UInt256) :
    accountStaticStateEq accounts
      (accounts.insert owner { (accounts.findD owner default) with balance := balance }) := by
  apply accountStaticStateEq_of_storage_code
  · apply accountStorageStateEq_insert_preserve <;> rfl
  · apply accountCodeStateEq_insert_preserve
    rfl

private theorem balance_insert_after (before after : AccountMap) (owner : Address) (balance : UInt256)
    (frame : accountStaticStateEq before after) :
    accountStaticStateEq after
      (after.insert owner { (before.findD owner default) with balance := balance }) := by
  apply accountStaticStateEq_of_storage_code
  · apply accountStorageStateEq_insert_preserve
    · exact (frame owner).1
    · exact (frame owner).2.1
  · apply accountCodeStateEq_insert_preserve
    exact (frame owner).2.2

/-- The opcode's account update changes balances but keeps code and storage. -/
theorem destruction_static_state (accounts : AccountMap) (sender receiver : Address) (created : Bool) :
    accountStaticStateEq accounts (destructionAccounts accounts sender receiver created) := by
  cases ownerFound : accounts.find? sender with
  | none => simpa only [destructionAccounts, ownerFound] using accountStaticStateEq_refl accounts
  | some owner =>
    have ownerDefault : accounts.findD sender default = owner := by
      simp [Batteries.RBMap.findD, ownerFound]
    cases targetFound : accounts.find? receiver with
    | none =>
      have targetDefault : accounts.findD receiver default = default := by
        simp [Batteries.RBMap.findD, targetFound]
      by_cases zero : owner.balance == (⟨0⟩ : UInt256)
      · simpa only [destructionAccounts, ownerFound, targetFound, zero, if_true]
          using accountStaticStateEq_refl accounts
      · have first := balance_insert_static accounts receiver owner.balance
        have second := balance_insert_after accounts _ sender ⟨0⟩ first
        have result := accountStaticStateEq_trans first second
        simpa only [destructionAccounts, ownerFound, targetFound, zero, if_false,
          ownerDefault, targetDefault] using result
    | some target =>
      have targetDefault : accounts.findD receiver default = target := by
        simp [Batteries.RBMap.findD, targetFound]
      by_cases different : receiver ≠ sender
      · have first := balance_insert_static accounts receiver (target.balance + owner.balance)
        have second := balance_insert_after accounts _ sender ⟨0⟩ first
        have result := accountStaticStateEq_trans first second
        simp only [destructionAccounts, ownerFound, targetFound]
        rw [if_pos different]
        simpa only [ownerDefault, targetDefault] using result
      · cases created with
        | false =>
          simpa only [destructionAccounts, ownerFound, targetFound, different, if_false]
            using accountStaticStateEq_refl accounts
        | true =>
          have first := balance_insert_static accounts receiver ⟨0⟩
          have second := balance_insert_after accounts _ sender ⟨0⟩ first
          have result := accountStaticStateEq_trans first second
          simpa only [destructionAccounts, ownerFound, targetFound, different, if_false, if_true,
            ownerDefault, targetDefault] using result

/-- The actual self-destruct step keeps every account's code and storage. -/
theorem selfdestruct_step_static {before after : Ethereum.State} {cost : Nat}
    {arg : Option (UInt256 × Nat)}
    (run : step cost (.SELFDESTRUCT, arg) before = .ok after) :
    accountStaticStateEq before.accountMap after.accountMap := by
  obtain ⟨receiver, accounts⟩ := selfdestruct_accounts run
  rw [accounts]
  exact destruction_static_state _ _ receiver _

end Rollup.EVM
