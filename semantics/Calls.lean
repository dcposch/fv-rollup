import semantics.Model

namespace Rollup

inductive Getter where
  | sequencer | stateRoot | batchNumber | backing
  | pendingDeposits (owner : Address)
  | pendingWithdrawals (owner : Address)
  deriving DecidableEq

inductive Entry where
  | deposit (owner : Address)
  | executeBatch (batch : Batch)
  | withdrawPendingBalance (owner : Address) (amount : Nat)
  | read (getter : Getter)

structure Call where
  caller : Address
  value : Nat
  entry : Entry

inductive ReturnValue where
  | unit
  | address (value : Address)
  | word (value : Nat)
  | root (value : Root)
  deriving DecidableEq

inductive CallOutcome where
  | success (value : ReturnValue)
  | revert
  | exceptional
  deriving DecidableEq

/-- Record a committed payment. The receiver can spend it during the callback. -/
structure PaymentEffect where
  owner : Address
  amount : Nat
  deriving DecidableEq

def readGetter (s : State) : Getter → ReturnValue
  | .sequencer => .address s.sequencer
  | .stateRoot => .root s.root
  | .batchNumber => .word s.batchNumber
  | .backing => .word s.backing
  | .pendingDeposits a => .word (s.pending a)
  | .pendingWithdrawals a => .word (s.claims a)

/-- Match a completed call to its actual caller, value, and arguments. -/
inductive CallStep : State → Call → CallOutcome → List PaymentEffect → State → Prop where
  | deposit {s caller owner value} (enabled : DepositEnabled s owner value) :
      CallStep s ⟨caller, value, .deposit owner⟩ (.success .unit) [] (deposit s owner value)
  | batch {s caller b} (enabled : BatchEnabled s caller b) :
      CallStep s ⟨caller, 0, .executeBatch b⟩ (.success .unit) [] (executeBatch s b)
  | withdrawal {s caller owner amount middle}
      (enabled : WithdrawalEnabled s owner amount)
      (callback : Callback (beginWithdrawal s owner amount) middle) :
      CallStep s ⟨caller, 0, .withdrawPendingBalance owner amount⟩ (.success .unit)
        [⟨owner, amount⟩] (finishWithdrawal middle ⟨owner, amount, s.eth⟩)
  | read (s caller getter) :
      CallStep s ⟨caller, 0, .read getter⟩ (.success (readGetter s getter)) [] s
  | revert (s call) : CallStep s call .revert [] s
  | exceptional (s call) : CallStep s call .exceptional [] s

/-- An environment can add ETH between calls without creating credit. -/
inductive TraceStep : State → State → Prop where
  | call {s t call outcome payments} : CallStep s call outcome payments t → TraceStep s t
  | donation {s amount} (bound : s.eth + amount < wordLimit) : TraceStep s (donate s amount)

inductive CallTrace (start : State) : State → Prop where
  | initial : CallTrace start start
  | next {s t} : CallTrace start s → TraceStep s t → CallTrace start t

end Rollup
