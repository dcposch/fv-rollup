import proofs.CallInstructionTree
import proofs.CreationInstructionTree
import proofs.LocalBoundary
import proofs.DestructionBoundary

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- These seven opcodes are the only instructions that enter children or destroy an account. -/
theorem nonlocal_operation_cases {op : Operation} (nonlocal : ¬ LocalOperation op) :
    (op = .CALL ∨ op = .CALLCODE ∨ op = .DELEGATECALL ∨ op = .STATICCALL) ∨
    (op = .CREATE ∨ op = .CREATE2) ∨ op = .SELFDESTRUCT := by
  cases op <;> rename_i command <;> cases command <;> simp_all [LocalOperation]

/-- A foreign instruction refines the boundary model when its recorded children do. -/
theorem instruction_tree_refines {before after : Ethereum.State} {jumps : Array UInt256} {ret}
    {self : Address} {keys : AccessScope} (children : InstructionChildren jumps before)
    (ordinary : self ∉ π) (foreign : self ≠ before.executionEnv.codeOwner)
    (ready : BoundaryReady self before.accountMap keys)
    (safe : Safe (boundaryModel self before.accountMap keys))
    (covered : children.covered self keys) (refined : children.refines self keys)
    (run : Xstep jumps before = .ok (after, ret)) :
    BoundaryRefines self keys before.accountMap after.accountMap := by
  rcases decoded : (decode before.executionEnv.code before.machineState.pc).getD (.STOP, none) with ⟨op, arg⟩
  by_cases internal : LocalOperation op
  · obtain ⟨next, same⟩ := local_instruction_boundary internal foreign ready decoded run
    exact ⟨next, same ▸ safe, same ▸ CallTrace.initial⟩
  · have frames := recorded_child_frames_refine children refined
    rcases nonlocal_operation_cases internal with calls | creations | rfl
    · exact call_instruction_tree_refines children ordinary foreign decoded calls ready safe covered frames run
    · exact creation_instruction_tree_refines foreign decoded creations ready safe frames run
    · exact selfdestruct_instruction_refines foreign ready safe decoded run

end Rollup.EVM
