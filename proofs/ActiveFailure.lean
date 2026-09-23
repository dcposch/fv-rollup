import semantics.ActivePrefix
import proofs.CreationTransfer

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- Invalid entry code cannot advance or enter a nested frame. -/
theorem active_prefix_invalid_entry {start current : Ethereum.State}
    (code : start.executionEnv.code = ⟨#[0xfe]⟩) (counter : start.machineState.pc = ⟨0⟩)
    (trace : ActivePrefix start current) : current = start := by
  have failed := invalid_entry_error start (D_J start.executionEnv.code 0) code counter
  have decoded : decode start.executionEnv.code start.machineState.pc = some (.INVALID, none) := by
    rw [code, counter]
    decide +kernel
  cases trace with
  | within earlier => exact instruction_prefix_entry_error failed earlier
  | call earlier entered active =>
    have same := continuing_prefix_entry_error failed earlier
    subst_vars
    cases entered with
    | entered instruction precheck arguments enabled selected =>
      simp only [decoded, Option.getD_some, Prod.mk.injEq] at instruction
      rcases instruction with ⟨rfl, rfl⟩
      simp [Z, δ] at precheck
  | creation earlier entered active =>
    have same := continuing_prefix_entry_error failed earlier
    subst_vars
    cases entered with
    | entered instruction precheck arguments bounded allowed =>
      simp only [decoded, Option.getD_some, Prod.mk.injEq] at instruction
      rcases instruction with ⟨rfl, rfl⟩
      simp [Z, δ] at precheck

/-- A colliding creation has no nested execution after the initialization entry. -/
theorem creation_collision_active_prefix (call : CreationCall) {current : Ethereum.State}
    (collision : call.collision = true) (trace : ActivePrefix call.entryState current) :
    current = call.entryState := by
  apply active_prefix_invalid_entry _ rfl trace
  simp only [CreationCall.entryState, CreationCall.environment, collision, if_true]

/-- The complete active tree of a colliding creation preserves the reservation. -/
theorem creation_collision_active_safe (call : CreationCall) {self : Address} {current : Ethereum.State}
    (keys : AccessScope) (payment : Payment) (foreign : self ≠ call.sender)
    (funds : call.value.toNat ≤ ethLedger call.accounts call.sender)
    (initial : LockedWorld self call.accounts)
    (safe : Safe (inFlightProjection (accountView self call.accounts) self keys payment))
    (collision : call.collision = true) (trace : ActivePrefix call.entryState current) :
    Safe (inFlightProjection current self keys payment) := by
  rw [creation_collision_active_prefix call collision trace]
  exact creation_transfer_safe call keys payment foreign funds initial safe

end Rollup.EVM
