import proofs.RuntimeBytecode

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Rollup.EVM

/-- A revert or gas failure excludes successful execution. -/
theorem rd_revert_no_success {code : ByteArray} {g : Sat256} {start : Ethereum.State}
    (rejected : RDrev code g start) (after : Ethereum.State) (output : ByteArray) :
    X (g.toNat + 1) (D_J code 0) start ≠ .ok (.success after output) := by
  intro success
  rcases rejected with failed | ⟨gas, data, reverted⟩
  · rw [success] at failed
    cases failed
  · rw [success] at reverted
    cases reverted

/-- Successful code execution has a matching successful instruction trace. -/
theorem xi_success_execution {cA gh bl σ σ₀ A I} {g : UInt256}
    {cA' σ' gas substate output}
    (success : Ξ cA gh bl σ σ₀ g A I = .ok (.success (cA', σ', gas, substate) output)) :
    ∃ state, X (g.toNat + 1) (D_J I.code 0)
      (initState cA gh bl σ σ₀ (.ofUInt256 g) A I) = .ok (.success state output) := by
  simp only [Ξ, bind, Except.bind] at success
  split at success
  · contradiction
  · rename_i result execute
    cases result with
    | revert gas data => simp at success
    | success state data =>
      simp only [Except.ok.injEq, ExecutionResult.success.injEq] at success
      rw [← success.2]
      exact ⟨state, execute⟩

/-- Static execution cannot pass the precheck for a storage write. -/
theorem static_sstore_precheck (state : Ethereum.State) (jumps : Array UInt256)
    (readonly : state.executionEnv.perm = false) (after : Ethereum.State × Nat) :
    Z jumps .SSTORE state ≠ .ok after := by
  unfold Z
  simp only [readonly]
  repeat' first | split | simp_all

/-- Reaching a storage write in static mode excludes successful execution. -/
theorem static_sstore_no_success (state : Ethereum.State) (jumps : Array UInt256)
    (readonly : state.executionEnv.perm = false)
    (decoded : decode state.executionEnv.code state.machineState.pc = some (.SSTORE, .none))
    (fuel : Nat) (after : Ethereum.State) (output : ByteArray) :
    X fuel jumps state ≠ .ok (.success after output) := by
  have failed : ∃ error, Xstep jumps state = .error error := by
    simp only [Xstep, decoded, Option.getD_some]
    cases checked : Z jumps .SSTORE state with
    | error error => exact ⟨error, rfl⟩
    | ok result => exact False.elim (static_sstore_precheck state jumps readonly result checked)
  obtain ⟨error, step⟩ := failed
  cases fuel with
  | zero => simp [X]
  | succ fuel => simp [X, step, bind, Except.bind]

/-- A reached storage write excludes success for the whole static execution. -/
theorem rd_sstore_static_no_success {code : ByteArray} {env : ExecutionEnv} {g : Sat256}
    {start : Ethereum.State} {pc : UInt256} {stack : List UInt256} {memory data : ByteArray}
    {words : UInt256} {accounts : Batteries.RBSet AccountAddress compare × AccountMap} {k cost : Nat}
    (reached : RD code env g start pc stack memory words data accounts k cost)
    (readonly : env.perm = false) (decoded : decode code pc = some (.SSTORE, .none))
    (after : Ethereum.State) (output : ByteArray) :
    X (g.toNat + 1) (D_J code 0) start ≠ .ok (.success after output) := by
  intro success
  rcases reached with failed | ⟨state, run, bytes, counter, _, _, _, _, _, _, _, _, environment, _⟩
  · rw [success] at failed
    cases failed
  · apply static_sstore_no_success state (D_J code 0) (by rw [environment]; exact readonly)
      (by rw [bytes, counter]; exact decoded) _ after output
    exact run.symm.trans success

end Rollup.EVM
