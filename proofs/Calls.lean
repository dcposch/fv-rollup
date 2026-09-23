import semantics.Calls
import proofs.Transitions

namespace Rollup

theorem callback_reachable {s t : State} (h : Callback s t) : Reachable s t := by
  induction h with
  | refl => exact .refl
  | donation _ _ bound ih => exact .next ih (.donation bound)

theorem reachable_trans {s t u : State} (left : Reachable s t) (right : Reachable t u) :
    Reachable s u := by
  induction right with
  | refl => exact left
  | next _ step ih => exact .next ih step

theorem callStep_reachable {s t : State} {call : Call} {outcome : CallOutcome}
    {payments : List PaymentEffect} (h : CallStep s call outcome payments t) : Reachable s t := by
  cases h with
  | deposit enabled => exact .next .refl (.deposit enabled)
  | batch enabled => exact .next .refl (.batch enabled)
  | withdrawal enabled callback =>
    have hp := (callback_preserves_storage callback).2.2.2.2.2.2.2.1
    exact .next (reachable_trans (.next .refl (.begin enabled)) (callback_reachable callback))
      (.finish hp)
  | read => exact .refl
  | revert => exact .refl
  | exceptional => exact .refl

theorem callStep_safe {s t : State} {call : Call} {outcome : CallOutcome}
    {payments : List PaymentEffect} (safe : Safe s)
    (h : CallStep s call outcome payments t) : Safe t :=
  reachable_safe safe (callStep_reachable h)

theorem callStep_idle {s t : State} {call : Call} {outcome : CallOutcome}
    {payments : List PaymentEffect} (idle : s.payment = none)
    (h : CallStep s call outcome payments t) : t.payment = none := by
  cases h with
  | deposit => exact idle
  | batch => exact idle
  | withdrawal => rfl
  | read => exact idle
  | revert => exact idle
  | exceptional => exact idle

theorem callTrace_safe {s t : State} (safe : Safe s) (h : CallTrace s t) : Safe t := by
  induction h with
  | initial => exact safe
  | next _ step ih =>
    cases step with
    | call call => exact callStep_safe ih call
    | donation bound => exact donation_safe ih bound

theorem callTrace_idle {s t : State} (idle : s.payment = none) (h : CallTrace s t) :
    t.payment = none := by
  induction h with
  | initial => exact idle
  | next _ step ih =>
    cases step with
    | call call => exact callStep_idle ih call
    | donation => exact ih

theorem callTrace_custody {self sequencer : Address} {root : Root} {eth : Nat} {s : State}
    (bound : eth < wordLimit) (trace : CallTrace (initial self sequencer root eth) s) :
    liabilities s ≤ s.eth := by
  have safe := callTrace_safe (initial_safe self sequencer root eth bound) trace
  have idle := callTrace_idle (by rfl) trace
  simpa [Solvent, reserved, idle] using safe.1

theorem successful_deposit_exact {s t : State} {caller owner : Address} {value : Nat}
    {result : ReturnValue} {payments : List PaymentEffect}
    (h : CallStep s ⟨caller, value, .deposit owner⟩ (.success result) payments t) :
    DepositEnabled s owner value ∧ t = deposit s owner value ∧ result = .unit ∧ payments = [] := by
  cases h with
  | deposit enabled => exact ⟨enabled, rfl, rfl, rfl⟩

theorem successful_batch_exact {s t : State} {caller : Address} {value : Nat} {b : Batch}
    {result : ReturnValue} {payments : List PaymentEffect}
    (h : CallStep s ⟨caller, value, .executeBatch b⟩ (.success result) payments t) :
    value = 0 ∧ BatchEnabled s caller b ∧ t = executeBatch s b ∧ result = .unit ∧ payments = [] := by
  cases h with
  | batch enabled => exact ⟨rfl, enabled, rfl, rfl, rfl⟩

/-- Successful batch authorization refers to the caller on this call label. -/
theorem successful_batch_authorized {s t : State} {caller : Address} {value : Nat} {b : Batch}
    {result : ReturnValue} {payments : List PaymentEffect}
    (h : CallStep s ⟨caller, value, .executeBatch b⟩ (.success result) payments t) :
    caller = s.sequencer := (successful_batch_exact h).2.1.2.1

theorem successful_withdrawal_payment {s t : State} {caller owner : Address} {value amount : Nat}
    {result : ReturnValue} {payments : List PaymentEffect}
    (h : CallStep s ⟨caller, value, .withdrawPendingBalance owner amount⟩
      (.success result) payments t) :
    value = 0 ∧ WithdrawalEnabled s owner amount ∧ result = .unit ∧ payments = [⟨owner, amount⟩] := by
  cases h with
  | withdrawal enabled _ => exact ⟨rfl, enabled, rfl, rfl⟩

theorem reverted_call_unchanged {s t : State} {call : Call} {payments : List PaymentEffect}
    (h : CallStep s call .revert payments t) : t = s ∧ payments = [] := by
  cases h
  exact ⟨rfl, rfl⟩

theorem exceptional_call_unchanged {s t : State} {call : Call} {payments : List PaymentEffect}
    (h : CallStep s call .exceptional payments t) : t = s ∧ payments = [] := by
  cases h
  exact ⟨rfl, rfl⟩

theorem callTrace_batch_number_monotone {s t : State} (h : CallTrace s t) :
    s.batchNumber ≤ t.batchNumber := by
  induction h with
  | initial => exact Nat.le_refl _
  | next _ step ih =>
    cases step with
    | call call => exact Nat.le_trans ih (reachable_batch_number_monotone (callStep_reachable call))
    | donation => exact ih

/-- A batch cannot be replayed after any later completed model calls. -/
theorem batch_cannot_replay_after_trace {s t : State} {caller : Address} {b : Batch}
    (trace : CallTrace (executeBatch s b) t) : ¬ BatchEnabled t caller b := by
  have mono := callTrace_batch_number_monotone trace
  intro enabled
  have number := enabled.2.2.1
  simp only [executeBatch] at mono
  omega

end Rollup
