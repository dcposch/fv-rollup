import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Fintype.BigOperators

namespace Rollup

abbrev Address := Fin (2 ^ 160)
abbrev Root := Fin (2 ^ 256)
def wordLimit : Nat := 2 ^ 256
abbrev Ledger := Address → Nat

noncomputable def total (ledger : Ledger) : Nat := ∑ a, ledger a

def credit (ledger : Ledger) (owner : Address) (amount : Nat) : Ledger :=
  Function.update ledger owner (ledger owner + amount)

def debit (ledger : Ledger) (owner : Address) (amount : Nat) : Ledger :=
  Function.update ledger owner (ledger owner - amount)

/-- Record the ETH in flight and the balance before the call. -/
structure Payment where
  owner : Address
  amount : Nat
  balanceBefore : Nat
  deriving DecidableEq

structure State where
  self : Address
  sequencer : Address
  root : Root
  batchNumber : Nat
  pending : Ledger
  claims : Ledger
  backing : Nat
  eth : Nat
  payment : Option Payment

structure Batch where
  number : Nat
  oldRoot : Root
  newRoot : Root
  depositOwner : Address
  depositAmount : Nat
  withdrawalOwner : Address
  withdrawalAmount : Nat

def initial (self sequencer : Address) (root : Root) (eth : Nat := 0) : State :=
  ⟨self, sequencer, root, 0, fun _ => 0, fun _ => 0, 0, eth, none⟩

def validOwner (s : State) (a : Address) : Prop := a ≠ 0 ∧ a ≠ s.self

def optionalOwner (s : State) (a : Address) (amount : Nat) : Prop :=
  if amount = 0 then a = 0 else validOwner s a

def DepositEnabled (s : State) (owner : Address) (amount : Nat) : Prop :=
  s.payment = none ∧ validOwner s owner ∧ 0 < amount ∧
  s.pending owner + amount < wordLimit ∧ s.eth + amount < wordLimit

def BatchEnabled (s : State) (caller : Address) (b : Batch) : Prop :=
  s.payment = none ∧ caller = s.sequencer ∧
  b.number = s.batchNumber + 1 ∧ b.number < wordLimit ∧ b.oldRoot = s.root ∧
  optionalOwner s b.depositOwner b.depositAmount ∧
  optionalOwner s b.withdrawalOwner b.withdrawalAmount ∧
  b.depositAmount ≤ s.pending b.depositOwner ∧
  s.backing + b.depositAmount < wordLimit ∧
  b.withdrawalAmount ≤ s.backing + b.depositAmount ∧
  s.claims b.withdrawalOwner + b.withdrawalAmount < wordLimit

def WithdrawalEnabled (s : State) (owner : Address) (amount : Nat) : Prop :=
  s.payment = none ∧ 0 < amount ∧ amount ≤ s.claims owner ∧ amount ≤ s.eth

def deposit (s : State) (owner : Address) (amount : Nat) : State :=
  { s with pending := credit s.pending owner amount, eth := s.eth + amount }

def executeBatch (s : State) (b : Batch) : State :=
  { s with pending := debit s.pending b.depositOwner b.depositAmount
           claims := credit s.claims b.withdrawalOwner b.withdrawalAmount
           backing := s.backing + b.depositAmount - b.withdrawalAmount
           root := b.newRoot, batchNumber := b.number }

/-- Transfer ETH. Keep the withdrawal credit until the call returns. -/
def beginWithdrawal (s : State) (owner : Address) (amount : Nat) : State :=
  { s with eth := s.eth - amount, payment := some ⟨owner, amount, s.eth⟩ }

def donate (s : State) (amount : Nat) : State := { s with eth := s.eth + amount }

def finishWithdrawal (s : State) (p : Payment) : State :=
  { s with claims := debit s.claims p.owner p.amount, payment := none }

/-- Restore the balance if the receiver call fails. Discard callback donations. -/
def abortWithdrawal (s : State) (p : Payment) : State :=
  { s with eth := p.balanceBefore, payment := none }

/-- This relation models callbacks. The EVM proof must establish its completeness. -/
inductive Callback : State → State → Prop where
  | refl (s) : Callback s s
  | donation {s t} (h : Callback s t) (amount : Nat)
      (bound : t.eth + amount < wordLimit) : Callback s (donate t amount)

/-- Each step is a completed call, except for the explicit withdrawal phases. -/
inductive Step : State → State → Prop where
  | deposit {s owner amount} (h : DepositEnabled s owner amount) :
      Step s (deposit s owner amount)
  | batch {s caller b} (h : BatchEnabled s caller b) : Step s (executeBatch s b)
  | begin {s owner amount} (h : WithdrawalEnabled s owner amount) :
      Step s (beginWithdrawal s owner amount)
  | donation {s amount} (bound : s.eth + amount < wordLimit) : Step s (donate s amount)
  | finish {s p} (h : s.payment = some p) : Step s (finishWithdrawal s p)
  | abort {s p} (h : s.payment = some p) : Step s (abortWithdrawal s p)
  | rejected (s) : Step s s

inductive Reachable (start : State) : State → Prop where
  | refl : Reachable start start
  | next {s t} : Reachable start s → Step s t → Reachable start t

end Rollup
