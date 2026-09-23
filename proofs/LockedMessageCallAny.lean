import proofs.LockedMessageCall
import proofs.LockedRuntimeAny

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Rollup.EVM

/-- An accepted call while locked changes only the incoming ETH transfer. -/
theorem locked_message_call_accepted_any (c : MessageCall)
    (created : Batteries.RBSet AccountAddress compare) (accounts : AccountMap)
    (gas : UInt256) (substate : Substate) (output : ByteArray)
    (locked : solcSlotWord c.accounts (c.environment runtimeBytecode) ⟨6⟩ ≠ ⟨0⟩)
    (accepted : c.run runtimeBytecode = (created, accounts, gas, substate, true, output)) :
    c.contextValue = ⟨0⟩ ∧ created = c.created ∧ accounts = c.initialAccounts := by
  have storage := (message_call_initial_static_state c c.receiver).1
  have stillLocked : solcSlotWord c.initialAccounts (c.environment runtimeBytecode) ⟨6⟩ ≠ ⟨0⟩ := by
    rw [solc_slot_default] at locked ⊢
    exact storage ▸ locked
  have execution := (message_call_accepted c runtimeBytecode created accounts gas substate output accepted).1
  exact locked_runtime_xi_preserves_accounts_any (g := .ofUInt256 c.gas) rfl stillLocked execution

/-- All calls into locked runtime code preserve code and storage, even on failure. -/
theorem locked_message_call_static_state_any (c : MessageCall)
    (created : Batteries.RBSet AccountAddress compare) (accounts : AccountMap)
    (gas : UInt256) (substate : Substate) (accepted : Bool) (output : ByteArray)
    (locked : solcSlotWord c.accounts (c.environment runtimeBytecode) ⟨6⟩ ≠ ⟨0⟩)
    (run : c.run runtimeBytecode = (created, accounts, gas, substate, accepted, output)) :
    accountStaticStateEq c.accounts accounts := by
  cases accepted with
  | false =>
    rw [(message_call_rejected c runtimeBytecode created accounts gas substate output run).1]
    exact accountStaticStateEq_refl _
  | true =>
    rw [(locked_message_call_accepted_any c created accounts gas substate output locked run).2.2]
    exact message_call_initial_static_state c

end Rollup.EVM
