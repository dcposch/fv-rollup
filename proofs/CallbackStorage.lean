import proofs.CallbackFrame
import proofs.LockedMessageCallAny

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Rollup.EVM

/-- A call into the locked rollup keeps its code and storage. -/
theorem locked_own_call_frame
    {blobs cA gh bl accounts original substate sender origin self gas price value contextValue
      calldata depth header writable cA' after gas' substate' accepted output}
    (pinned : (accounts.findD self default).code = runtimeBytecode)
    (locked : (accounts.findD self default).storage.findD ⟨6⟩ ⟨0⟩ ≠ ⟨0⟩)
    (run : Θ blobs cA gh bl accounts original substate sender origin self
      (toExecute accounts self) gas price value contextValue calldata depth header writable =
      (cA', after, gas', substate', accepted, output)) :
    CodeStorageFrame self accounts after := by
  by_cases precompile : self ∈ π
  · have selected : toExecute accounts self = .Precompiled self := by
      simp [toExecute, precompile]
    rw [selected] at run
    exact accountStaticStateEq_of_precompiled_Theta run self
  ·
    let call : MessageCall := {
      blobs := blobs, created := cA, genesis := gh, blocks := bl, accounts := accounts,
      original := original, substate := substate, sender := sender, origin := origin,
      receiver := self, gas := gas, gasPrice := price, value := value,
      contextValue := contextValue, calldata := calldata, depth := depth,
      header := header, writable := writable }
    have selected := pinned_toExecute precompile pinned
    rw [selected] at run
    have locked' : solcSlotWord call.accounts (call.environment runtimeBytecode) ⟨6⟩ ≠ ⟨0⟩ := by
      rw [solc_slot_default]
      exact locked
    exact locked_message_call_static_state_any call cA' after gas' substate' accepted output
      locked' run self

/-- Each locality step preserves locked rollup code and storage. -/
theorem locked_locality_step {self : AccountAddress} {accounts after : AccountMap}
    (pinned : (accounts.findD self default).code = runtimeBytecode)
    (locked : (accounts.findD self default).storage.findD ⟨6⟩ ⟨0⟩ ≠ ⟨0⟩)
    (step : account_change_consistent self accounts after) :
    CodeStorageFrame self accounts after := by
  cases step with
  | unchanged same => exact pinned_unchanged_frame pinned same
  | init_dead dead => exact (pinned_account_not_dead pinned dead).elim
  | call_prelude => exact sendEth_accountStaticStateEq _ _ _ _ _ self
  | create_prelude => exact sendEthCreate_static_state _ _ _ _ _ self
  | @by_own_code blobs cA cA' gh bl before original after substate substate'
      sender origin gas gas' price value contextValue calldata output depth header writable accepted run =>
    have transfer : CodeStorageFrame self before (sendEth self sender value accepted before) :=
      sendEth_accountStaticStateEq self sender value accepted before self
    have beforePinned : (before.findD self default).code = runtimeBytecode :=
      transfer.2.2.trans pinned
    have beforeLocked : (before.findD self default).storage.findD ⟨6⟩ ⟨0⟩ ≠ ⟨0⟩ := by
      rw [transfer.1]
      exact locked
    exact transfer.symm.trans (locked_own_call_frame beforePinned beforeLocked run)
  | by_own_code_from_start run => exact locked_own_call_frame pinned locked run

/-- Any chain of locality steps preserves locked rollup code and storage. -/
theorem locked_locality_chain {self : AccountAddress} {accounts after : AccountMap}
    (pinned : (accounts.findD self default).code = runtimeBytecode)
    (locked : (accounts.findD self default).storage.findD ⟨6⟩ ⟨0⟩ ≠ ⟨0⟩)
    (chain : account_changes_consistent self accounts after) :
    CodeStorageFrame self accounts after := by
  induction chain with
  | refl => exact CodeStorageFrame.refl self accounts
  | @tail during after chain step frame =>
    have duringPinned : (during.findD self default).code = runtimeBytecode :=
      frame.2.2.symm.trans pinned
    have duringLocked : (during.findD self default).storage.findD ⟨6⟩ ⟨0⟩ ≠ ⟨0⟩ := by
      rw [← frame.1]
      exact locked
    exact frame.trans (locked_locality_step duringPinned duringLocked step)

/-- Arbitrary call chains preserve the locked rollup's code and storage. -/
theorem callback_preserves_rollup_storage
    {blobs cA gh bl accounts original substate sender origin receiver gas price value contextValue
      calldata depth header writable cA' after gas' substate' accepted output}
    (self : AccountAddress)
    (pinned : (accounts.findD self default).code = runtimeBytecode)
    (locked : (accounts.findD self default).storage.findD ⟨6⟩ ⟨0⟩ ≠ ⟨0⟩)
    (run : Θ blobs cA gh bl accounts original substate sender origin receiver
      (toExecute accounts receiver) gas price value contextValue calldata depth header writable =
      (cA', after, gas', substate', accepted, output)) :
    CodeStorageFrame self accounts after := by
  exact locked_locality_chain pinned locked
    (account_changes_consistent_of_Theta cA' after gas' substate' accepted output depth run self)

end Rollup.EVM
