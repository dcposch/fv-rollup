import proofs.WorldBalances

open Ethereum Ethereum.EVM Reasoning.Theory

namespace Rollup.EVM

def creditEthAccounts (accounts : AccountMap) (receiver : Address) (value : UInt256) : AccountMap :=
  match accounts.find? receiver with
  | none => if value != UInt256.ofNat 0 then
      accounts.insert receiver { (default : Account) with balance := value }
    else accounts
  | some account => accounts.insert receiver { account with balance := account.balance + value }

def debitEthAccounts (accounts : AccountMap) (sender : Address) (value : UInt256) : AccountMap :=
  match accounts.find? sender with
  | none => accounts
  | some account => accounts.insert sender { account with balance := account.balance - value }

theorem sendEth_split (accounts : AccountMap) (receiver sender : Address) (value : UInt256) :
    sendEth receiver sender value true accounts =
      debitEthAccounts (creditEthAccounts accounts receiver value) sender value := rfl

theorem ethLedger_credit (accounts : AccountMap) (receiver : Address) (value : UInt256)
    (bounded : ethLedger accounts receiver + value.toNat < UInt256.size) :
    ethLedger (creditEthAccounts accounts receiver value) = credit (ethLedger accounts) receiver value.toNat := by
  cases found : accounts.find? receiver with
  | none =>
    have old : ethLedger accounts receiver = 0 := by
      rw [ethLedger_lookup, found]
      rfl
    by_cases zero : value = ⟨0⟩
    · subst value
      simp [creditEthAccounts, found, credit, UInt256.toNat,
        show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from rfl]
    · have nonzero : (value != UInt256.ofNat 0) = true := by
        change (value != (⟨0⟩ : UInt256)) = true
        simp [zero]
      simp only [creditEthAccounts, found, nonzero, if_true, ethLedger_insert, credit, old, Nat.zero_add]
  | some account =>
    have old : ethLedger accounts receiver = account.balance.toNat := by
      simp [ethLedger, Batteries.RBMap.findD, found]
    simp only [creditEthAccounts, found, ethLedger_insert, credit, old]
    congr 1
    rw [uadd_toNat, Nat.mod_eq_of_lt (by simpa only [old] using bounded)]

theorem ethLedger_debit (accounts : AccountMap) (sender : Address) (value : UInt256)
    (funds : value.toNat ≤ ethLedger accounts sender) :
    ethLedger (debitEthAccounts accounts sender value) = debit (ethLedger accounts) sender value.toNat := by
  cases found : accounts.find? sender with
  | none =>
    have old : ethLedger accounts sender = 0 := by rw [ethLedger_lookup, found]; rfl
    have amount : value.toNat = 0 := by omega
    simp [debitEthAccounts, found, debit, amount]
  | some account =>
    have old : ethLedger accounts sender = account.balance.toNat := by
      simp [ethLedger, Batteries.RBMap.findD, found]
    simp only [debitEthAccounts, found, ethLedger_insert, debit, old]
    congr 1
    exact usub_toNat (by simpa only [old] using funds)

/-- A funded transfer has the exact debit and credit when the accounts differ. -/
theorem sendEth_ledger_ne (accounts : AccountMap) (receiver sender : Address) (value : UInt256)
    (different : receiver ≠ sender)
    (funds : value.toNat ≤ ethLedger accounts sender)
    (world : worldEth accounts < wordLimit) :
    ethLedger (sendEth receiver sender value true accounts) =
      debit (credit (ethLedger accounts) receiver value.toNat) sender value.toNat := by
  have creditBalance := ethLedger_credit accounts receiver value
    (funded_recipient_bound accounts receiver sender value different funds world)
  rw [sendEth_split, ethLedger_debit, creditBalance]
  rw [creditBalance]
  simpa [credit, Function.update_of_ne (Ne.symm different)] using funds

/-- A funded transfer between distinct accounts conserves total ETH. -/
theorem sendEth_world_ne (accounts : AccountMap) (receiver sender : Address) (value : UInt256)
    (different : receiver ≠ sender)
    (funds : value.toNat ≤ ethLedger accounts sender)
    (world : worldEth accounts < wordLimit) :
    worldEth (sendEth receiver sender value true accounts) = worldEth accounts := by
  have covered : value.toNat ≤ credit (ethLedger accounts) receiver value.toNat sender := by
    simpa [credit, Function.update_of_ne (Ne.symm different)] using funds
  have debitTotal := total_debit (credit (ethLedger accounts) receiver value.toNat) sender value.toNat covered
  rw [total_credit] at debitTotal
  unfold worldEth
  rw [sendEth_ledger_ne accounts receiver sender value different funds world]
  omega

private theorem word_add_sub_cancel (first second : UInt256) :
    first + second - second = first := by
  change (⟨(first.val + second.val) - second.val⟩ : UInt256) = first
  rw [add_sub_cancel_right]

private theorem word_sub_self (value : UInt256) : value - value = ⟨0⟩ := by
  change (⟨value.val - value.val⟩ : UInt256) = ⟨0⟩
  rw [sub_self]

/-- A transfer to the sender preserves every balance, including modular addition. -/
theorem sendEth_self_ledger (accounts : AccountMap) (owner : Address) (value : UInt256) :
    ethLedger (sendEth owner owner value true accounts) = ethLedger accounts := by
  rw [sendEth_split]
  cases found : accounts.find? owner with
  | none =>
    have old : ethLedger accounts owner = 0 := by rw [ethLedger_lookup, found]; rfl
    simp only [creditEthAccounts, found]
    split
    · simp only [debitEthAccounts, accountMap_find_insert_self, word_sub_self, ethLedger_insert]
      simp [old, UInt256.toNat]
    · simp only [debitEthAccounts, found]
  | some account =>
    have old : ethLedger accounts owner = account.balance.toNat := by
      simp [ethLedger, Batteries.RBMap.findD, found]
    simp only [creditEthAccounts, found, debitEthAccounts, accountMap_find_insert_self,
      word_add_sub_cancel, ethLedger_insert]
    simp [← old]

/-- Funded message-call transfers conserve total ETH. -/
theorem sendEth_world (accounts : AccountMap) (receiver sender : Address) (value : UInt256)
    (accepted : Bool) (funds : value.toNat ≤ ethLedger accounts sender)
    (world : worldEth accounts < wordLimit) :
    worldEth (sendEth receiver sender value accepted accounts) = worldEth accounts := by
  cases accepted with
  | false => rfl
  | true =>
    by_cases same : receiver = sender
    · subst receiver
      exact congrArg total (sendEth_self_ledger accounts sender value)
    · exact sendEth_world_ne accounts receiver sender value same funds world

/-- A funded transfer cannot reduce another account's ETH balance. -/
theorem sendEth_other_balance (accounts : AccountMap) (receiver sender self : Address)
    (value : UInt256) (accepted : Bool) (different : self ≠ sender)
    (funds : value.toNat ≤ ethLedger accounts sender)
    (world : worldEth accounts < wordLimit) :
    ethLedger accounts self ≤ ethLedger (sendEth receiver sender value accepted accounts) self := by
  cases accepted with
  | false => exact Nat.le_refl _
  | true =>
    by_cases same : receiver = sender
    · subst receiver
      rw [sendEth_self_ledger]
    · rw [sendEth_ledger_ne accounts receiver sender value same funds world]
      simp only [debit, Function.update_of_ne different]
      by_cases target : self = receiver
      · subst self
        simp [credit]
      · simp [credit, Function.update_of_ne target]

/-- A zero-value transfer preserves all balances, including the sender's balance. -/
theorem sendEth_zero_ledger (accounts : AccountMap) (receiver sender : Address) (accepted : Bool) :
    ethLedger (sendEth receiver sender ⟨0⟩ accepted accounts) = ethLedger accounts := by
  cases accepted with
  | false => rfl
  | true =>
    have bound : ethLedger accounts receiver + (⟨0⟩ : UInt256).toNat < UInt256.size := by
      change (accounts.findD receiver default).balance.val.val + 0 < UInt256.size
      exact (accounts.findD receiver default).balance.val.isLt
    rw [sendEth_split, ethLedger_debit _ _ _ (Nat.zero_le _), ethLedger_credit _ _ _ bound]
    simp [credit, debit, UInt256.toNat]

/-- Zero-value call variants also protect the source account's balance. -/
theorem sendEth_protected_balance (accounts : AccountMap) (receiver sender self : Address)
    (value : UInt256) (accepted : Bool) (safeSender : self ≠ sender ∨ value = ⟨0⟩)
    (funds : value.toNat ≤ ethLedger accounts sender)
    (world : worldEth accounts < wordLimit) :
    ethLedger accounts self ≤ ethLedger (sendEth receiver sender value accepted accounts) self := by
  rcases safeSender with different | rfl
  · exact sendEth_other_balance accounts receiver sender self value accepted different funds world
  · rw [sendEth_zero_ledger]

/-- An outgoing transfer cannot debit more than its stated amount. -/
theorem sendEth_sender_lower_bound (accounts : AccountMap) (receiver sender : Address)
    (value : UInt256) (accepted : Bool) (funds : value.toNat ≤ ethLedger accounts sender)
    (world : worldEth accounts < wordLimit) :
    ethLedger accounts sender - value.toNat ≤
      ethLedger (sendEth receiver sender value accepted accounts) sender := by
  cases accepted with
  | false => exact Nat.sub_le _ _
  | true =>
    by_cases same : receiver = sender
    · subst receiver
      rw [sendEth_self_ledger]
      exact Nat.sub_le _ _
    · rw [sendEth_ledger_ne accounts receiver sender value same funds world]
      simp [debit, credit, Function.update_of_ne (Ne.symm same)]

end Rollup.EVM
