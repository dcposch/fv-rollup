import semantics.Model

namespace Rollup

noncomputable def liabilities (s : State) : Nat := total s.pending + s.backing + total s.claims

def reserved (s : State) : Nat := (s.payment.map Payment.amount).getD 0

/-- Include ETH in flight while the receiver call is active. -/
def Solvent (s : State) : Prop := liabilities s ≤ s.eth + reserved s

/-- The saved balance can back all credit if the receiver call fails. -/
def PaymentSafe (s : State) : Prop :=
  ∀ p, s.payment = some p →
    0 < p.amount ∧ p.amount ≤ s.claims p.owner ∧ liabilities s ≤ p.balanceBefore

def WordBounded (s : State) : Prop :=
  s.batchNumber < wordLimit ∧ s.backing < wordLimit ∧ s.eth < wordLimit ∧
  (∀ a, s.pending a < wordLimit) ∧ (∀ a, s.claims a < wordLimit) ∧
  (∀ p, s.payment = some p → p.balanceBefore < wordLimit)

def Safe (s : State) : Prop := Solvent s ∧ PaymentSafe s ∧ WordBounded s

end Rollup
