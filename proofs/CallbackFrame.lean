import semantics.AccountFrame
import semantics.Bytecode
import Ethereum.Theory.AccountLocality
import Ethereum.Theory.StaticStorage

open Ethereum Ethereum.EVM

namespace Rollup.EVM

theorem CodeStorageFrame.refl (self : AccountAddress) (accounts : AccountMap) :
    CodeStorageFrame self accounts accounts := ⟨rfl, rfl, rfl⟩

theorem CodeStorageFrame.symm {self before after}
    (frame : CodeStorageFrame self before after) : CodeStorageFrame self after before :=
  ⟨frame.1.symm, frame.2.1.symm, frame.2.2.symm⟩

theorem CodeStorageFrame.trans {self before during after}
    (first : CodeStorageFrame self before during)
    (second : CodeStorageFrame self during after) : CodeStorageFrame self before after :=
  ⟨first.1.trans second.1, first.2.1.trans second.2.1, first.2.2.trans second.2.2⟩

/-- The creation value transfer keeps all code and storage. -/
theorem sendEthCreate_static_state (a sender : AccountAddress) (value : UInt256)
    (accepted : Bool) (accounts : AccountMap) :
    accountStaticStateEq accounts (sendEthCreate a sender value accepted accounts) := by
  cases accepted with
  | false => exact accountStaticStateEq_refl accounts
  | true =>
    cases found : accounts.find? sender with
    | none => simp [sendEthCreate, found]
    | some account =>
      let debited := accounts.insert sender { account with balance := account.balance - value }
      have first : accountStaticStateEq accounts debited := by
        apply accountStaticStateEq_of_storage_code
        · apply accountStorageStateEq_insert_preserve <;>
            simp [Batteries.RBMap.findD, found]
        · apply accountCodeStateEq_insert_preserve
          simp [Batteries.RBMap.findD, found]
      rw [sendEthCreate_true_find?_some a sender value accounts account found]
      apply accountStaticStateEq_trans first
      apply accountStaticStateEq_of_storage_code
      · apply accountStorageStateEq_insert_preserve
        · exact (first a).1
        · exact (first a).2.1
      · apply accountCodeStateEq_insert_preserve
        exact (first a).2.2

/-- A pinned rollup account exists and has nonempty code. -/
theorem pinned_account_present {accounts : AccountMap} {self : AccountAddress}
    (pinned : (accounts.findD self default).code = runtimeBytecode) :
    ∃ account, accounts.find? self = some account ∧ account.code = runtimeBytecode := by
  cases found : accounts.find? self with
  | none =>
    have nonempty : runtimeBytecode ≠ (default : Account).code := by decide +kernel
    simp only [Batteries.RBMap.findD, found, Option.getD_none] at pinned
    exact (nonempty pinned.symm).elim
  | some account =>
    exact ⟨account, rfl, by simpa [Batteries.RBMap.findD, found] using pinned⟩

/-- Stored runtime code is selected outside the precompile address set. -/
theorem pinned_toExecute {accounts : AccountMap} {self : AccountAddress}
    (ordinary : self ∉ π)
    (pinned : (accounts.findD self default).code = runtimeBytecode) :
    toExecute accounts self = .Code runtimeBytecode := by
  obtain ⟨account, found, code⟩ := pinned_account_present pinned
  simp [toExecute, ordinary, found, code, Id.run]

/-- The locality relation keeps a live account's code and storage. -/
theorem pinned_unchanged_frame {accounts after : AccountMap} {self : AccountAddress}
    (pinned : (accounts.findD self default).code = runtimeBytecode)
    (same : unchanged self accounts after) : CodeStorageFrame self accounts after := by
  obtain ⟨account, found, code⟩ := pinned_account_present pinned
  cases same with
  | null absent => simp [found] at absent
  | empty acc present nonce empty storage =>
    have eq : acc = account := Option.some.inj (present.symm.trans found)
    subst acc
    rw [code] at empty
    have size : runtimeBytecode.size = 1429 := by decide +kernel
    omega
  | present acc acc' present present' nonce code' storage tstorage balance =>
    exact ⟨by simpa [Batteries.RBMap.findD, present, present'] using storage,
      by simpa [Batteries.RBMap.findD, present, present'] using tstorage,
      by simpa [Batteries.RBMap.findD, present, present'] using code'⟩

theorem pinned_account_not_dead {accounts : AccountMap} {self : AccountAddress}
    (pinned : (accounts.findD self default).code = runtimeBytecode) :
    ¬ account_dead accounts self := by
  obtain ⟨account, found, code⟩ := pinned_account_present pinned
  intro dead
  simp only [account_dead, found] at dead
  have empty := dead.2.1
  rw [code] at empty
  have size : runtimeBytecode.size = 1429 := by decide +kernel
  omega

end Rollup.EVM
