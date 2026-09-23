import proofs.support.LockedFrame
import proofs.LockedPathRows
import proofs.AbstractInstruction
import proofs.FrameCertificate

open Ethereum Ethereum.EVM

set_option maxRecDepth 100000

namespace Rollup.EVM

/-- The checked table is an account-preserving invariant for the locked runtime. -/
def lockedFrameCertificate (jumps : Array UInt256) : AccountFrameCertificate jumps where
  accepts := LockedFrameReady
  operation := by
    intro state ready
    obtain ⟨code, locked, cursor, member, represented⟩ := ready
    exact locked_cursor_neutral member code represented
  continues := by
    intro before after ready run
    obtain ⟨code, locked, cursor, member, represented⟩ := ready
    obtain ⟨next, advance, closed⟩ := path_certificate_row (locked_paths_row cursor member)
    have actualAdvance : cursor.successors
        ((decode before.executionEnv.code cursor.pc).getD (.STOP, none)).1
        ((decode before.executionEnv.code cursor.pc).getD (.STOP, none)).2 = some next := by
      rw [code]
      exact advance
    obtain ⟨following, nextMember, known⟩ :=
      abstract_instruction_sound represented locked actualAdvance run
    have accounts := account_preserving_instruction (locked_cursor_neutral member code represented) rfl run
    have environment := Xstep_env_unchanged before after jumps none run
    have afterCode : after.executionEnv.code = runtimeBytecode := by rwa [← environment]
    have afterLocked : (after.sload ⟨6⟩).2 ≠ ⟨0⟩ := by
      simpa only [Ethereum.State.sload, Ethereum.State.lookupAccount, accounts, ← environment] using locked
    exact ⟨afterCode, afterLocked, following, closed following nextMember, known⟩

/-- A fresh execution of the locked runtime starts in the checked table. -/
theorem locked_frame_initial {state : Ethereum.State}
    (code : state.executionEnv.code = runtimeBytecode) (counter : state.machineState.pc = ⟨0⟩)
    (stack : state.machineState.stack = []) (locked : (state.sload ⟨6⟩).2 ≠ ⟨0⟩) :
    LockedFrameReady state := by
  refine ⟨code, locked, ⟨⟨0⟩, []⟩, locked_paths_initial, counter, ?_⟩
  change List.Forall₂ AbstractWord.denotes [] state.machineState.stack
  rw [stack]
  exact List.Forall₂.nil

/-- The locked rollup cannot change any account at an active execution prefix. -/
theorem locked_active_accounts {start current : Ethereum.State}
    (code : start.executionEnv.code = runtimeBytecode) (counter : start.machineState.pc = ⟨0⟩)
    (stack : start.machineState.stack = []) (locked : (start.sload ⟨6⟩).2 ≠ ⟨0⟩)
    (trace : ActivePrefix start current) : current.accountMap = start.accountMap := by
  exact frame_certificate_active start current (lockedFrameCertificate _)
    (locked_frame_initial code counter stack locked) trace

end Rollup.EVM
