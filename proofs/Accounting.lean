import invariants.Invariants
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace Rollup

open scoped BigOperators

theorem total_credit (ledger : Ledger) (owner : Address) (amount : Nat) :
    total (credit ledger owner amount) = total ledger + amount := by
  classical
  simp only [total, credit, Finset.sum_update_of_mem (Finset.mem_univ owner)]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ owner)]
  simp [Finset.sdiff_singleton_eq_erase, Nat.add_assoc, Nat.add_comm]

theorem total_debit (ledger : Ledger) (owner : Address) (amount : Nat)
    (h : amount ≤ ledger owner) :
    total (debit ledger owner amount) + amount = total ledger := by
  classical
  simp only [total, debit, Finset.sum_update_of_mem (Finset.mem_univ owner)]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ owner)]
  simp only [Finset.sdiff_singleton_eq_erase]
  omega

theorem balance_le_total (ledger : Ledger) (owner : Address) : ledger owner ≤ total ledger := by
  exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ owner)

theorem initial_safe (self sequencer : Address) (root : Root) (eth : Nat)
    (bound : eth < wordLimit) : Safe (initial self sequencer root eth) := by
  simp [Safe, Solvent, PaymentSafe, WordBounded, initial, liabilities, total, reserved,
    wordLimit] at *
  exact bound

theorem deposit_solvent {s : State} (safe : Solvent s) (owner : Address) (amount : Nat) :
    Solvent (deposit s owner amount) := by
  unfold Solvent liabilities at *
  simp only [deposit, total_credit, reserved] at *
  omega

theorem batch_solvent {s : State} {caller : Address} {b : Batch}
    (safe : Solvent s) (enabled : BatchEnabled s caller b) :
    Solvent (executeBatch s b) := by
  obtain ⟨_, _, _, _, _, _, _, hd, _, hw, _⟩ := enabled
  have ht := total_debit s.pending b.depositOwner b.depositAmount hd
  unfold Solvent liabilities at *
  simp only [executeBatch, total_credit, reserved] at *
  omega

theorem deposit_liabilities (s : State) (owner : Address) (amount : Nat) :
    liabilities (deposit s owner amount) = liabilities s + amount := by
  simp only [liabilities, deposit, total_credit]
  omega

theorem batch_conserves_liabilities {s : State} {caller : Address} {b : Batch}
    (enabled : BatchEnabled s caller b) :
    liabilities (executeBatch s b) = liabilities s := by
  obtain ⟨_, _, _, _, _, _, _, hd, _, hw, _⟩ := enabled
  have ht := total_debit s.pending b.depositOwner b.depositAmount hd
  simp only [liabilities, executeBatch, total_credit]
  omega

theorem finish_liabilities {s : State} {p : Payment}
    (safe : PaymentSafe s) (hp : s.payment = some p) :
    liabilities (finishWithdrawal s p) + p.amount = liabilities s := by
  have ht := total_debit s.claims p.owner p.amount (safe p hp).2.1
  simp only [liabilities, finishWithdrawal]
  omega

theorem begin_solvent {s : State} {owner : Address} {amount : Nat}
    (safe : Solvent s) (enabled : WithdrawalEnabled s owner amount) :
    Solvent (beginWithdrawal s owner amount) := by
  obtain ⟨idle, _, _, funds⟩ := enabled
  simp [Solvent, liabilities, reserved, idle, beginWithdrawal] at *
  omega

theorem donation_solvent {s : State} (safe : Solvent s) (amount : Nat) :
    Solvent (donate s amount) := by
  unfold Solvent liabilities reserved at *
  simp only [donate] at *
  omega

theorem finish_solvent {s : State} {p : Payment}
    (safe : Solvent s) (paymentSafe : PaymentSafe s) (hp : s.payment = some p) :
    Solvent (finishWithdrawal s p) := by
  have debitBound := (paymentSafe p hp).2.1
  have ht := total_debit s.claims p.owner p.amount debitBound
  simp only [Solvent, liabilities, reserved, hp, Option.map_some, Option.getD_some] at safe
  simp only [Solvent, liabilities, finishWithdrawal, reserved, Option.map_none,
    Option.getD_none, Nat.add_zero]
  omega

theorem abort_solvent {s : State} {p : Payment}
    (paymentSafe : PaymentSafe s) (hp : s.payment = some p) :
    Solvent (abortWithdrawal s p) := by
  simpa [Solvent, liabilities, reserved, abortWithdrawal] using (paymentSafe p hp).2.2

end Rollup
