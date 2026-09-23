import semantics.CreationCall
import proofs.CallbackFrame
import proofs.PrefixFailure

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- Creation code execution starts at the exact initialization state. -/
theorem creation_execute_entry (call : CreationCall) :
    call.execute = (do
      let result ← X (call.gas.toNat + 1) (D_J call.environment.code 0) call.entryState
      match result with
      | .success state output =>
        pure (.success (state.createdAccounts, state.accountMap,
          state.machineState.gasAvailable.toUInt256, state.substate) output)
      | .revert gas output => pure (.revert gas output)) := by
  unfold CreationCall.execute Ξ
  rfl

/-- A creation address with the pinned rollup code fails the collision check. -/
theorem creation_pinned_collision (call : CreationCall) {self : Address}
    (pinned : (call.accounts.findD self default).code = runtimeBytecode)
    (same : call.address = self) : call.collision = true := by
  have size : runtimeBytecode.size = 1429 := by decide +kernel
  simp [CreationCall.collision, same, pinned, size]

/-- A creation that passes the collision check cannot use the rollup's address. -/
theorem creation_fresh_foreign (call : CreationCall) {self : Address}
    (pinned : (call.accounts.findD self default).code = runtimeBytecode)
    (fresh : call.collision = false) : self ≠ call.address := by
  intro same
  have collision := creation_pinned_collision call pinned same.symm
  rw [fresh] at collision
  cases collision

/-- A collision fails on the first initialization instruction. -/
theorem creation_collision_entry_error (call : CreationCall) (jumps : Array UInt256)
    (collision : call.collision = true) :
    Xstep jumps call.entryState = .error .InvalidInstruction := by
  apply invalid_entry_error
  · simp only [CreationCall.entryState, CreationCall.environment, collision, if_true]
  · rfl

/-- A colliding creation has no prefix after its initialization entry. -/
theorem creation_collision_prefix (call : CreationCall) {current : Ethereum.State}
    (collision : call.collision = true)
    (trace : InstructionPrefix (D_J call.environment.code 0) call.entryState current) :
    current = call.entryState :=
  instruction_prefix_entry_error (creation_collision_entry_error call _ collision) trace

/-- The collision stub makes initialization fail, for any gas amount. -/
theorem creation_collision_execute (call : CreationCall) (collision : call.collision = true) :
    call.execute = .error .InvalidInstruction := by
  rw [creation_execute_entry]
  simp only [X, creation_collision_entry_error call _ collision, bind, Except.bind]

/-- An initialization error restores the creation input accounts. -/
theorem creation_call_error (call : CreationCall) (error : ExecutionException)
    (execution : call.execute = .error error) :
    call.run = (call.address, call.initialCreated, call.accounts, ⟨0⟩,
      call.substate.addAccessedAccount call.address, false, ByteArray.empty) := by
  unfold CreationCall.execute CreationCall.initialCreated CreationCall.initialAccounts
    CreationCall.environment CreationCall.collision CreationCall.address Deployment.address at execution
  unfold CreationCall.run Lambda
  dsimp only at execution ⊢
  simp only [apply_ite] at execution ⊢
  erw [execution]
  rfl

/-- An initialization revert also restores accounts and retains its remaining gas. -/
theorem creation_call_revert (call : CreationCall) (gas : UInt256) (output : ByteArray)
    (execution : call.execute = .ok (.revert gas output)) :
    call.run = (call.address, call.initialCreated, call.accounts, gas,
      call.substate.addAccessedAccount call.address, false, output) := by
  unfold CreationCall.execute CreationCall.initialCreated CreationCall.initialAccounts
    CreationCall.environment CreationCall.collision CreationCall.address Deployment.address at execution
  unfold CreationCall.run Lambda
  dsimp only at execution ⊢
  simp only [apply_ite] at execution ⊢
  erw [execution]
  rfl

/-- Every accepted creation contains a successful initialization execution. -/
theorem creation_call_accepted (call : CreationCall)
    {address created accounts gas substate output}
    (run : call.run = (address, created, accounts, gas, substate, true, output)) :
    ∃ initCreated initAccounts initGas initSubstate returned,
      call.execute = .ok (.success (initCreated, initAccounts, initGas, initSubstate) returned) := by
  cases execution : call.execute with
  | error error =>
    rw [creation_call_error call error execution] at run
    have impossible := congrArg (fun result => result.2.2.2.2.2.1) run
    cases impossible
  | ok result =>
    cases result with
    | revert gas data =>
      rw [creation_call_revert call gas data execution] at run
      have impossible := congrArg (fun result => result.2.2.2.2.2.1) run
      cases impossible
    | success result data =>
      obtain ⟨created, accounts, gas, substate⟩ := result
      exact ⟨created, accounts, gas, substate, data, rfl⟩

/-- Accepted creation passes the address collision check. -/
theorem creation_accepted_fresh (call : CreationCall)
    {address created accounts gas substate output}
    (run : call.run = (address, created, accounts, gas, substate, true, output)) :
    call.collision = false := by
  cases collision : call.collision with
  | false => rfl
  | true =>
    have execution := creation_collision_execute call collision
    rw [creation_call_error call .InvalidInstruction execution] at run
    have impossible := congrArg (fun result => result.2.2.2.2.2.1) run
    cases impossible

/-- A fresh creation cannot reuse the caller's incremented, nonzero nonce account. -/
theorem creation_fresh_not_sender (call : CreationCall)
    (nonce : (call.accounts.findD call.sender default).nonce ≠ ⟨0⟩)
    (fresh : call.collision = false) : call.address ≠ call.sender := by
  intro same
  unfold CreationCall.collision at fresh
  rw [same] at fresh
  simp [nonce] at fresh

end Rollup.EVM
