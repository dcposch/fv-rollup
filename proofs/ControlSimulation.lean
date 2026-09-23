import proofs.ControlStorage
import proofs.ControlMemory
import proofs.ControlCall
import proofs.AbstractExecution
import proofs.AbstractJump
import proofs.AbstractPush
import proofs.AbstractMemory
import proofs.AbstractDrop
import proofs.AbstractSwap

open Ethereum Ethereum.EVM

set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace Rollup.EVM

private def opcodeInput (before : Ethereum.State) (cost : Nat) : Ethereum.State :=
  { before with
    machineState.execLength := before.machineState.execLength + 1
    machineState.gasAvailable := before.machineState.gasAvailable.subNat cost }

/-- Every supported nonhalting opcode stays within its abstract successors. -/
theorem control_step_sound {cursor : AbstractCursor} {next : List AbstractCursor}
    {before after : Ethereum.State} {cost : Nat} {op : Operation} {arg : Option (UInt256 × Nat)}
    (represented : cursor.denotes before)
    (nonhalt : op ≠ .STOP ∧ op ≠ .RETURN ∧ op ≠ .REVERT ∧ op ≠ .INVALID)
    (advance : cursor.controlSuccessors op arg = some next)
    (run : step cost (op, arg) before = .ok after) :
    ∃ following ∈ next, following.denotes after := by
  have inputRepresented : cursor.denotes (opcodeInput before cost) := represented
  cases op
  case Push kind =>
    cases kind
    case PUSH0 =>
      simp only [AbstractCursor.controlSuccessors, AbstractCursor.successors, Option.some.injEq] at advance
      subst next
      exact ⟨_, List.mem_singleton_self _, abstract_push0_step represented run⟩
    all_goals
      cases arg with
      | none => simp [AbstractCursor.controlSuccessors, AbstractCursor.successors] at advance
      | some argument =>
        rcases argument with ⟨value, width⟩
        simp only [AbstractCursor.controlSuccessors, AbstractCursor.successors, bind, Option.bind, pure, Option.some.injEq] at advance
        subst next
        exact ⟨_, List.mem_singleton_self _, abstract_push_step (by decide) represented run⟩
  all_goals rename_i command
  all_goals cases command
  all_goals try (rcases nonhalt with ⟨a, b, c, d⟩; contradiction)
  all_goals simp only [AbstractCursor.controlSuccessors, AbstractCursor.successors] at advance
  all_goals try exact abstract_jumpIf_step represented advance run
  all_goals try
    obtain ⟨following, evolved, same⟩ := Option.map_eq_some_iff.mp advance
    subst next
    refine ⟨following, List.mem_singleton_self _, ?_⟩
  all_goals first
    | exact abstract_mload_step represented evolved run
    | exact abstract_mstore_step represented evolved run
    | exact control_sstore_step represented evolved run
    | exact control_returndatacopy_step represented evolved run
    | exact control_call_step represented evolved run
    | exact abstract_pop_step represented evolved run
    | exact abstract_keccak_step represented evolved run
    | exact abstract_jump_step represented evolved run
    | (simp only [step] at run
       first
       | exact abstract_execBinOp (before := opcodeInput before cost) _ inputRepresented evolved run
       | exact abstract_execUnOp (before := opcodeInput before cost) UInt256.isZero AbstractWord.isZero (fun _ _ h => abstract_isZero_sound h) inputRepresented evolved run
       | exact control_execSload (before := opcodeInput before cost) inputRepresented evolved run
       | exact abstract_execUnOp (before := opcodeInput before cost) UInt256.lnot (AbstractWord.unary UInt256.lnot) (fun _ _ h => abstract_unary_sound UInt256.lnot h) inputRepresented evolved run
       | exact abstract_unary_read (before := opcodeInput before cost) _ inputRepresented evolved run
       | exact abstract_duplicate (before := opcodeInput before cost) _ inputRepresented evolved run
       | exact abstract_exchange (before := opcodeInput before cost) _ (by decide) inputRepresented evolved run)
    | (cases Option.some.inj advance
       refine ⟨_, List.mem_singleton_self _, ?_⟩
       first
       | exact abstract_jumpdest_step represented run
       | (simp only [step] at run
          first
          | exact abstract_executionEnvOp (before := opcodeInput before cost) _ inputRepresented run
          | exact control_machineStateOp (before := opcodeInput before cost) _ inputRepresented run))

end Rollup.EVM
