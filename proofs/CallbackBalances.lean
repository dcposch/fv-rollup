import proofs.WorldCallSteps
import proofs.WorldCreationSteps
import proofs.WorldDepthLimit

open Ethereum Ethereum.EVM

namespace Rollup.EVM

private theorem next_depth_measure {depth : Fin 1025} {n : Nat}
    (remaining : 1024 - depth.val = n + 1) :
    1024 - (depth + 1).val = n := by
  have bounded := depth.isLt
  have next : (depth + 1).val = depth.val + 1 := by
    rw [Fin.val_add_eq_of_add_lt]
    simp
    omega
  omega

/-- All foreign opcodes preserve ETH without a callback-correctness premise. -/
theorem foreign_step_balances (self : Address) (depth : Fin 1025) :
    ForeignStepBalances self depth := by
  suffices allDepths : ∀ n (depth : Fin 1025), 1024 - depth.val = n →
      ForeignStepBalances self depth from allDepths _ depth rfl
  intro n
  induction n with
  | zero =>
    intro depth remaining
    have same : depth = 1024 := by
      apply Fin.ext
      have bound := depth.isLt
      change depth.val = 1024
      omega
    subst depth
    exact foreign_step_balances_at_limit self
  | succ n ih =>
    intro depth remaining before after gasCost instr atDepth foreign initial run
    rcases instr with ⟨op, arg⟩
    by_cases internal : LocalOperation op
    · have ledger := local_step_ethLedger internal run
      simp only [EthFrame, worldEth, ledger]
      exact ⟨Nat.le_refl _, Nat.le_refl _⟩
    by_cases destroy : op = .SELFDESTRUCT
    · subst op
      exact selfdestruct_step_balances self foreign (LockedWorld.bounded initial) run
    by_cases creates : op = .CREATE ∨ op = .CREATE2
    · apply creation_step_balances creates _ foreign initial run
      intro next nextValue
      apply protected_creation_balances_of_steps
      apply ih next
      rw [atDepth] at nextValue
      omega
    · have calls : op = .CALL ∨ op = .CALLCODE ∨ op = .DELEGATECALL ∨ op = .STATICCALL := by
        cases op <;> rename_i command <;> cases command <;> simp_all [LocalOperation]
      apply call_step_balances calls _ foreign initial run
      apply protected_call_balances_of_steps
      apply ih (before.executionEnv.depth + 1)
      rw [atDepth]
      exact next_depth_measure remaining

/-- Arbitrary code in another storage context cannot debit the locked rollup. -/
theorem foreign_execution_balances
    {self : Address} {cA gh bl accounts original gas substate env cA' after gas' substate' output}
    (foreign : self ≠ env.codeOwner)
    (initial : LockedWorld self accounts)
    (run : Ξ cA gh bl accounts original gas substate env =
      .ok (.success (cA', after, gas', substate') output)) :
    EthFrame self accounts after :=
  foreign_xi_balances (env := env) (run := run)
    (foreign_step_balances self env.depth) foreign initial

/-- Nested calls cannot create ETH or debit the locked rollup. -/
theorem callback_call_balances (self : Address) (depth : Fin 1025) :
    ProtectedCallBalances self depth :=
  protected_call_balances_of_steps (foreign_step_balances self depth)

/-- Nested creation cannot create ETH or debit the locked rollup. -/
theorem callback_creation_balances (self : Address) (depth : Fin 1025) :
    ProtectedCreationBalances self depth :=
  protected_creation_balances_of_steps (foreign_step_balances self depth)

end Rollup.EVM
