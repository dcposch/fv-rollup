import proofs.Safety

namespace Rollup

theorem batch_authorized {s : State} {caller : Address} {b : Batch}
    (h : BatchEnabled s caller b) : caller = s.sequencer := h.2.1

theorem batch_continuity {s : State} {caller : Address} {b : Batch}
    (h : BatchEnabled s caller b) : b.oldRoot = s.root ∧ b.number = s.batchNumber + 1 :=
  ⟨h.2.2.2.2.1, h.2.2.1⟩

theorem batch_cannot_replay (s : State) (caller : Address) (b : Batch) :
    ¬ BatchEnabled (executeBatch s b) caller b := by
  intro replay
  have number := replay.2.2.1
  simp only [executeBatch] at number
  omega

theorem credit_isolation (ledger : Ledger) (owner other : Address) (amount : Nat)
    (h : other ≠ owner) : credit ledger owner amount other = ledger other := by
  simp [credit, Function.update_of_ne h]

theorem debit_isolation (ledger : Ledger) (owner other : Address) (amount : Nat)
    (h : other ≠ owner) : debit ledger owner amount other = ledger other := by
  simp [debit, Function.update_of_ne h]

theorem batch_deposit_debit {s : State} {caller : Address} {b : Batch}
    (h : BatchEnabled s caller b) :
    (executeBatch s b).pending b.depositOwner + b.depositAmount = s.pending b.depositOwner := by
  have bound := h.2.2.2.2.2.2.2.1
  simp only [executeBatch, debit, Function.update_self]
  omega

theorem batch_withdrawal_credit (s : State) (b : Batch) :
    (executeBatch s b).claims b.withdrawalOwner =
      s.claims b.withdrawalOwner + b.withdrawalAmount := by
  simp [executeBatch, credit]

theorem withdrawal_exact_debit {s : State} {p : Payment}
    (h : PaymentSafe s) (hp : s.payment = some p) :
    (finishWithdrawal s p).claims p.owner + p.amount = s.claims p.owner := by
  have bound := (h p hp).2.1
  simp only [finishWithdrawal, debit, Function.update_self]
  omega

theorem locked_rejects_mutations {s : State} {p : Payment} (locked : s.payment = some p) :
    (∀ a n, ¬ DepositEnabled s a n) ∧
    (∀ caller b, ¬ BatchEnabled s caller b) ∧
    (∀ a n, ¬ WithdrawalEnabled s a n) := by
  constructor
  · intro a n h; simpa [locked] using h.1
  constructor
  · intro caller b h; simpa [locked] using h.1
  · intro a n h; simpa [locked] using h.1

theorem step_preserves_identity {s t : State} (h : Step s t) :
    t.self = s.self ∧ t.sequencer = s.sequencer := by
  cases h <;> exact ⟨rfl, rfl⟩

theorem batch_number_monotone {s t : State} (h : Step s t) : s.batchNumber ≤ t.batchNumber := by
  cases h with
  | batch h => simp only [executeBatch, h.2.2.1]; omega
  | _ => exact Nat.le_refl _

theorem reachable_batch_number_monotone {s t : State} (h : Reachable s t) :
    s.batchNumber ≤ t.batchNumber := by
  induction h with
  | refl => exact Nat.le_refl _
  | next _ step ih => exact Nat.le_trans ih (batch_number_monotone step)

theorem root_change_requires_batch {s t : State} (h : Step s t) (changed : t.root ≠ s.root) :
    ∃ caller b, BatchEnabled s caller b ∧ t = executeBatch s b := by
  cases h with
  | batch h => exact ⟨_, _, h, rfl⟩
  | _ => exact False.elim (changed rfl)

theorem callback_preserves_storage {s t : State} (h : Callback s t) :
    t.self = s.self ∧ t.sequencer = s.sequencer ∧ t.root = s.root ∧
    t.batchNumber = s.batchNumber ∧ t.pending = s.pending ∧ t.claims = s.claims ∧
    t.backing = s.backing ∧ t.payment = s.payment ∧ s.eth ≤ t.eth := by
  induction h with
  | refl => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, Nat.le_refl _⟩
  | donation _ amount _ ih =>
    obtain ⟨a, b, c, d, e, f, g, h, balance⟩ := ih
    exact ⟨a, b, c, d, e, f, g, h, by dsimp [donate]; omega⟩

theorem callback_preserves_safe {s t : State} (safe : Safe s) (h : Callback s t) : Safe t := by
  induction h with
  | refl => exact safe
  | donation _ _ bound ih => exact donation_safe ih bound

/-- A failed receiver call restores all rollup state in the model. -/
theorem failed_withdrawal_restores_state {s t : State} {owner : Address} {amount : Nat}
    (idle : s.payment = none) (h : Callback (beginWithdrawal s owner amount) t) :
    abortWithdrawal t ⟨owner, amount, s.eth⟩ = s := by
  obtain ⟨a, b, c, d, e, f, g, _, _⟩ := callback_preserves_storage h
  cases s
  cases t
  simp_all [abortWithdrawal, beginWithdrawal]

/-- A successful receiver call cannot increase any withdrawal credit. -/
theorem successful_withdrawal_exact {s t : State} {owner : Address} {amount : Nat}
    (enabled : WithdrawalEnabled s owner amount)
    (h : Callback (beginWithdrawal s owner amount) t) :
    (finishWithdrawal t ⟨owner, amount, s.eth⟩).claims = debit s.claims owner amount ∧
    (finishWithdrawal t ⟨owner, amount, s.eth⟩).eth + amount ≥ s.eth := by
  obtain ⟨_, _, _, _, _, claims, _, _, eth⟩ := callback_preserves_storage h
  have funds := enabled.2.2.2
  constructor
  · simp only [finishWithdrawal, claims, beginWithdrawal]
  · simp only [finishWithdrawal, beginWithdrawal] at *; omega

/-- Payment needs no sequencer call once withdrawal credit exists. -/
theorem credited_withdrawal_has_funds {s : State} {owner : Address} {amount : Nat}
    (safe : Safe s) (idle : s.payment = none) (positive : 0 < amount)
    (credit : amount ≤ s.claims owner) : WithdrawalEnabled s owner amount := by
  refine ⟨idle, positive, credit, ?_⟩
  have solv := safe.1
  have totalBound := balance_le_total s.claims owner
  simp [Solvent, reserved, idle, liabilities] at solv
  omega

end Rollup
