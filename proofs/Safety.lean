import proofs.Accounting

namespace Rollup

theorem credit_bounded {ledger : Ledger} {owner : Address} {amount : Nat}
    (h : ∀ a, ledger a < wordLimit) (bound : ledger owner + amount < wordLimit) :
    ∀ a, credit ledger owner amount a < wordLimit := by
  intro a
  by_cases ha : a = owner
  · subst a; simpa [credit] using bound
  · simpa [credit, Function.update_of_ne ha] using h a

theorem debit_bounded {ledger : Ledger} {owner : Address} {amount : Nat}
    (h : ∀ a, ledger a < wordLimit) :
    ∀ a, debit ledger owner amount a < wordLimit := by
  intro a
  by_cases ha : a = owner
  · subst a; simpa [debit] using lt_of_le_of_lt (Nat.sub_le (ledger owner) amount) (h owner)
  · simpa [debit, Function.update_of_ne ha] using h a

theorem deposit_safe {s : State} {owner : Address} {amount : Nat}
    (safe : Safe s) (enabled : DepositEnabled s owner amount) :
    Safe (deposit s owner amount) := by
  obtain ⟨solvent, _, number, backing, _, pending, claims, _⟩ := safe
  obtain ⟨idle, _, _, pendingBound, ethBound⟩ := enabled
  refine ⟨deposit_solvent solvent owner amount, ?_, ?_⟩
  · simp [PaymentSafe, deposit, idle]
  · exact ⟨number, backing, ethBound, credit_bounded pending pendingBound, claims,
      by simp [deposit, idle]⟩

theorem batch_safe {s : State} {caller : Address} {b : Batch}
    (safe : Safe s) (enabled : BatchEnabled s caller b) :
    Safe (executeBatch s b) := by
  obtain ⟨solvent, _, _, _, eth, pending, claims, _⟩ := safe
  have solv := batch_solvent solvent enabled
  obtain ⟨idle, _, _, number, _, _, _, _, backing, _, claimBound⟩ := enabled
  refine ⟨solv, ?_, ?_⟩
  · simp [PaymentSafe, executeBatch, idle]
  · exact ⟨number, lt_of_le_of_lt (Nat.sub_le _ _) backing, eth,
      debit_bounded pending, credit_bounded claims claimBound,
      by simp [executeBatch, idle]⟩

theorem begin_safe {s : State} {owner : Address} {amount : Nat}
    (safe : Safe s) (enabled : WithdrawalEnabled s owner amount) :
    Safe (beginWithdrawal s owner amount) := by
  obtain ⟨solvent, _, number, backing, eth, pending, claims, _⟩ := safe
  have solv := begin_solvent solvent enabled
  obtain ⟨idle, positive, creditBound, _⟩ := enabled
  refine ⟨solv, ?_, ?_⟩
  · intro p hp
    simp only [beginWithdrawal, Option.some.injEq] at hp
    subst p
    refine ⟨positive, creditBound, ?_⟩
    simpa [Solvent, reserved, idle, liabilities, beginWithdrawal] using solvent
  · refine ⟨number, backing, lt_of_le_of_lt (Nat.sub_le _ _) eth, pending, claims, ?_⟩
    intro p hp
    simp only [beginWithdrawal, Option.some.injEq] at hp
    subst p
    exact eth

theorem donation_safe {s : State} {amount : Nat}
    (safe : Safe s) (bound : s.eth + amount < wordLimit) : Safe (donate s amount) := by
  obtain ⟨solvent, payment, number, backing, _, pending, claims, saved⟩ := safe
  exact ⟨donation_solvent solvent amount, payment, number, backing, bound, pending, claims, saved⟩

theorem finish_safe {s : State} {p : Payment}
    (safe : Safe s) (hp : s.payment = some p) : Safe (finishWithdrawal s p) := by
  obtain ⟨solvent, payment, number, backing, eth, pending, claims, _⟩ := safe
  refine ⟨finish_solvent solvent payment hp, ?_, number, backing, eth,
    pending, debit_bounded claims, ?_⟩ <;> simp [PaymentSafe, finishWithdrawal]

theorem abort_safe {s : State} {p : Payment}
    (safe : Safe s) (hp : s.payment = some p) : Safe (abortWithdrawal s p) := by
  obtain ⟨_, payment, number, backing, _, pending, claims, saved⟩ := safe
  refine ⟨abort_solvent payment hp, ?_, number, backing, saved p hp,
    pending, claims, ?_⟩ <;> simp [PaymentSafe, abortWithdrawal]

theorem step_preserves_safe {s t : State} (safe : Safe s) (step : Step s t) : Safe t := by
  cases step with
  | deposit h => exact deposit_safe safe h
  | batch h => exact batch_safe safe h
  | begin h => exact begin_safe safe h
  | donation h => exact donation_safe safe h
  | finish h => exact finish_safe safe h
  | abort h => exact abort_safe safe h
  | rejected => exact safe

/-- The model is safe after any finite sequence of steps. -/
theorem reachable_safe {start s : State} (safe : Safe start) (h : Reachable start s) : Safe s := by
  induction h with
  | refl => exact safe
  | next _ step ih => exact step_preserves_safe ih step

theorem custody {self sequencer : Address} {root : Root} {eth : Nat} {s : State}
    (bound : eth < wordLimit) (h : Reachable (initial self sequencer root eth) s)
    (idle : s.payment = none) : liabilities s ≤ s.eth := by
  have hs := (reachable_safe (initial_safe self sequencer root eth bound) h).1
  simpa [Solvent, reserved, idle] using hs

end Rollup
