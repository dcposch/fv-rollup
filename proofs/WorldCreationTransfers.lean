import proofs.WorldTransfers

open Ethereum Ethereum.EVM Reasoning.Theory

namespace Rollup.EVM

/-- Creation debits the sender and credits the distinct new address. -/
theorem sendEthCreate_ledger_ne (accounts : AccountMap) (receiver sender : Address) (value : UInt256)
    (different : receiver ≠ sender)
    (funds : value.toNat ≤ ethLedger accounts sender)
    (world : worldEth accounts < wordLimit) :
    ethLedger (sendEthCreate receiver sender value true accounts) =
      credit (debit (ethLedger accounts) sender value.toNat) receiver value.toNat := by
  cases found : accounts.find? sender with
  | none =>
    have old : ethLedger accounts sender = 0 := by rw [ethLedger_lookup, found]; rfl
    have amount : value.toNat = 0 := by omega
    simp [sendEthCreate, found, credit, debit, amount]
  | some account =>
    have old : ethLedger accounts sender = account.balance.toNat := by
      simp [ethLedger, Batteries.RBMap.findD, found]
    have sub : (account.balance - value).toNat = account.balance.toNat - value.toNat :=
      usub_toNat (by simpa only [old] using funds)
    have add : (value + (accounts.findD receiver default).balance).toNat =
        value.toNat + ethLedger accounts receiver := by
      rw [uadd_toNat]
      exact Nat.mod_eq_of_lt (by
        have bounded := funded_recipient_bound accounts receiver sender value different funds world
        change _ < UInt256.size
        simpa only [ethLedger, Nat.add_comm] using bounded)
    rw [sendEthCreate_true_find?_some receiver sender value accounts account found]
    simp only [ethLedger_insert, sub, add, credit, debit, Function.update_of_ne different, old]
    rw [Nat.add_comm value.toNat]

/-- Funded creation transfers conserve total ETH at distinct addresses. -/
theorem sendEthCreate_world_ne (accounts : AccountMap) (receiver sender : Address) (value : UInt256)
    (accepted : Bool) (different : receiver ≠ sender)
    (funds : value.toNat ≤ ethLedger accounts sender)
    (world : worldEth accounts < wordLimit) :
    worldEth (sendEthCreate receiver sender value accepted accounts) = worldEth accounts := by
  cases accepted with
  | false => rfl
  | true =>
    unfold worldEth
    rw [sendEthCreate_ledger_ne accounts receiver sender value different funds world, total_credit]
    exact total_debit (ethLedger accounts) sender value.toNat funds

/-- Creation cannot debit an account other than its sender. -/
theorem sendEthCreate_other_balance (accounts : AccountMap) (receiver sender self : Address)
    (value : UInt256) (accepted : Bool) (newAddress : receiver ≠ sender) (different : self ≠ sender)
    (funds : value.toNat ≤ ethLedger accounts sender)
    (world : worldEth accounts < wordLimit) :
    ethLedger accounts self ≤ ethLedger (sendEthCreate receiver sender value accepted accounts) self := by
  cases accepted with
  | false => exact Nat.le_refl _
  | true =>
    rw [sendEthCreate_ledger_ne accounts receiver sender value newAddress funds world]
    by_cases target : self = receiver
    · subst self
      simp [credit, debit, Function.update_of_ne different]
    · simp [credit, debit, Function.update_of_ne target, Function.update_of_ne different]

end Rollup.EVM
