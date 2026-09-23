import semantics.MessageCall

open Ethereum Ethereum.EVM

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Rollup.EVM

/-- Revert restores accounts and substate, including the incoming ETH transfer. -/
theorem message_call_revert (c : MessageCall) (code : ByteArray) (gas : UInt256)
    (output : ByteArray)
    (execution : c.execute code = .ok (.revert gas output)) :
    c.run code = (c.created, c.accounts, gas, c.substate, false, output) := by
  unfold MessageCall.execute MessageCall.initialAccounts MessageCall.environment at execution
  dsimp only at execution
  unfold MessageCall.run
  unfold Θ
  dsimp only
  erw [execution]
  rfl

/-- An exceptional halt also consumes the call gas. -/
theorem message_call_error (c : MessageCall) (code : ByteArray) (error : EVM.ExecutionException)
    (execution : c.execute code = .error error) :
    c.run code = (c.created, c.accounts, ⟨0⟩, c.substate, false, ByteArray.empty) := by
  unfold MessageCall.execute MessageCall.initialAccounts MessageCall.environment at execution
  dsimp only at execution
  unfold MessageCall.run
  unfold Θ
  dsimp only
  erw [execution]
  rfl

/-- A successful execution commits its result when its account map is not empty. -/
theorem message_call_success (c : MessageCall) (code : ByteArray)
    (created : Batteries.RBSet AccountAddress compare) (accounts : AccountMap)
    (gas : UInt256) (substate : Substate) (output : ByteArray)
    (execution : c.execute code = .ok (.success (created, accounts, gas, substate) output))
    (nonempty : (accounts == ∅) = false) :
    c.run code = (created, accounts, gas, substate, true, output) := by
  unfold MessageCall.execute MessageCall.initialAccounts MessageCall.environment at execution
  dsimp only at execution
  unfold MessageCall.run Θ
  dsimp only
  erw [execution]
  simp only [nonempty, Bool.false_eq_true, if_false]

/-- A call cannot accept an empty execution result. -/
theorem message_call_empty (c : MessageCall) (code : ByteArray)
    (created : Batteries.RBSet AccountAddress compare) (accounts : AccountMap)
    (gas : UInt256) (substate : Substate) (output : ByteArray)
    (execution : c.execute code = .ok (.success (created, accounts, gas, substate) output))
    (empty : (accounts == ∅) = true) :
    c.run code = (created, c.accounts, gas, c.substate, false, output) := by
  unfold MessageCall.execute MessageCall.initialAccounts MessageCall.environment at execution
  dsimp only at execution
  unfold MessageCall.run Θ
  dsimp only
  erw [execution]
  simp only [empty, if_true]

/-- Every accepted message call has a matching successful EVM execution. -/
theorem message_call_accepted (c : MessageCall) (code : ByteArray)
    (created : Batteries.RBSet AccountAddress compare) (accounts : AccountMap)
    (gas : UInt256) (substate : Substate) (output : ByteArray)
    (accepted : c.run code = (created, accounts, gas, substate, true, output)) :
    c.execute code = .ok (.success (created, accounts, gas, substate) output) ∧
      (accounts == ∅) = false := by
  cases execution : c.execute code with
  | error error =>
    rw [message_call_error c code error execution] at accepted
    simp only [Prod.mk.injEq, Bool.false_eq_true, and_false, false_and] at accepted
  | ok result =>
    cases result with
    | revert gas' output' =>
      rw [message_call_revert c code gas' output' execution] at accepted
      simp only [Prod.mk.injEq, Bool.false_eq_true, and_false, false_and] at accepted
    | success result output' =>
      obtain ⟨created', accounts', gas', substate'⟩ := result
      cases empty : accounts' == ∅ with
      | true =>
        rw [message_call_empty c code created' accounts' gas' substate' output' execution empty] at accepted
        simp only [Prod.mk.injEq, Bool.false_eq_true, and_false, false_and] at accepted
      | false =>
        rw [message_call_success c code created' accounts' gas' substate' output' execution empty] at accepted
        cases accepted
        exact ⟨rfl, empty⟩

/-- A rejected message call restores its input accounts and substate. -/
theorem message_call_rejected (c : MessageCall) (code : ByteArray)
    (created : Batteries.RBSet AccountAddress compare) (accounts : AccountMap)
    (gas : UInt256) (substate : Substate) (output : ByteArray)
    (rejected : c.run code = (created, accounts, gas, substate, false, output)) :
    accounts = c.accounts ∧ substate = c.substate := by
  cases execution : c.execute code with
  | error error =>
    rw [message_call_error c code error execution] at rejected
    cases rejected
    exact ⟨rfl, rfl⟩
  | ok result =>
    cases result with
    | revert gas' output' =>
      rw [message_call_revert c code gas' output' execution] at rejected
      cases rejected
      exact ⟨rfl, rfl⟩
    | success result output' =>
      obtain ⟨created', accounts', gas', substate'⟩ := result
      cases empty : accounts' == ∅ with
      | true =>
        rw [message_call_empty c code created' accounts' gas' substate' output' execution empty] at rejected
        cases rejected
        exact ⟨rfl, rfl⟩
      | false =>
        rw [message_call_success c code created' accounts' gas' substate' output' execution empty] at rejected
        simp only [Prod.mk.injEq, Bool.true_eq_false, and_false, false_and] at rejected

end Rollup.EVM
