import proofs.support.PrefixReach
import proofs.PrefixPush
import proofs.InstructionContinue

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Rollup.EVM

/-- Start symbolic prefix execution from the actual fresh EVM frame. -/
theorem PCR.initState {code : ByteArray} {environment : ExecutionEnv} {target child : Ethereum.State}
    {created genesis blocks accounts original gas substate}
    (codeEq : environment.code = code)
    (trace : ContinuingPrefix (D_J code 0)
      (initState created genesis blocks accounts original gas substate environment) target)
    (entered : ChildCallEntry (D_J code 0) target child) :
    PCR code environment target child ⟨0⟩ [] ByteArray.empty ⟨0⟩ ByteArray.empty (created, accounts) := by
  refine ⟨codeEq, ?_⟩
  rw [← codeEq] at trace entered
  exact prefix_cursor_initial
    (start := Reasoning.Theory.initState created genesis blocks accounts original gas substate environment)
    trace entered

/-- A stack-only cost-three instruction advances the exact symbolic prefix. -/
theorem PCR.stepStack {code : ByteArray} {environment : ExecutionEnv} {target child : Ethereum.State}
    {pc : UInt256} {memory : ByteArray} {words : UInt256} {returnData : ByteArray}
    {accounts : Batteries.RBSet AccountAddress compare × AccountMap} {input output : List UInt256}
    {op : Operation} {arg : Option (UInt256 × Nat)}
    (reached : PCR code environment target child pc input memory words returnData accounts)
    (decoded : decode code pc = some (op, arg))
    (noncall : op ≠ .CALL ∧ op ≠ .CALLCODE ∧ op ≠ .DELEGATECALL ∧ op ≠ .STATICCALL)
    (execution : ∀ state : Ethereum.State, state.executionEnv.code = code → state.machineState.pc = pc →
      state.machineState.stack = input → Xstep (D_J code 0) state =
        if state.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
        else .ok (stSwap state output, none)) :
    PCR code environment target child (pc + ⟨1⟩) output memory words returnData accounts := by
  refine ⟨reached.1, ?_⟩
  apply prefix_cursor_guarded (op := op) (arg := arg) reached.2
    (by simp only [reached.1, decoded, Option.getD_some]) noncall
    (fun state => state.machineState.gasAvailable.toNat < 3) (fun state => stSwap state output)
  · intro state matched
    rw [reached.1]
    exact execution state ((congrArg ExecutionEnv.code matched.1).trans reached.1) matched.2.1 matched.2.2.1
  · intro state matched
    exact ⟨matched.1, congrArg (fun value => value + ⟨1⟩) matched.2.1, rfl,
      matched.2.2.2⟩

/-- A halting instruction cannot precede the known child within the same frame. -/
theorem PCR.halt {code : ByteArray} {environment : ExecutionEnv} {target child : Ethereum.State}
    {pc : UInt256} {stack : List UInt256} {memory : ByteArray} {words : UInt256} {returnData : ByteArray}
    {accounts : Batteries.RBSet AccountAddress compare × AccountMap}
    {op : Operation} {arg : Option (UInt256 × Nat)}
    (reached : PCR code environment target child pc stack memory words returnData accounts)
    (decoded : decode code pc = some (op, arg))
    (halt : op = .STOP ∨ op = .RETURN ∨ op = .REVERT ∨ op = .INVALID) : False := by
  have noncall : op ≠ .CALL ∧ op ≠ .CALLCODE ∧ op ≠ .DELEGATECALL ∧ op ≠ .STATICCALL := by
    rcases halt with rfl | rfl | rfl | rfl <;> decide
  apply prefix_cursor_stopped (op := op) (arg := arg) reached.2
    (by simp only [reached.1, decoded, Option.getD_some]) noncall
  intro before after matched run
  have actual : (decode before.executionEnv.code before.machineState.pc).getD (.STOP, none) = (op, arg) := by
    simp only [matched.1, matched.2.1, reached.1, decoded, Option.getD_some]
  have continuing := continuing_instruction_kind actual run
  rcases halt with same | same | same | same
  · exact continuing.1 same
  · exact continuing.2.1 same
  · exact continuing.2.2.1 same
  · exact continuing.2.2.2 same

end Rollup.EVM
