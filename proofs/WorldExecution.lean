import proofs.CallbackExecutionStorage
import proofs.WorldPrecheck
import Ethereum.Theory.ProgressLemmas

open Ethereum Ethereum.EVM

set_option maxRecDepth 2048

namespace Rollup.EVM

/-- A callback cannot create ETH or debit the protected account. -/
def EthFrame (self : Address) (before after : AccountMap) : Prop :=
  worldEth after ≤ worldEth before ∧ ethLedger before self ≤ ethLedger after self

theorem EthFrame.refl (self : Address) (accounts : AccountMap) :
    EthFrame self accounts accounts := ⟨Nat.le_refl _, Nat.le_refl _⟩

theorem EthFrame.trans {self before during after}
    (first : EthFrame self before during) (second : EthFrame self during after) :
    EthFrame self before after :=
  ⟨second.1.trans first.1, first.2.trans second.2⟩

/-- These conditions are carried through each callback step. -/
structure LockedWorld (self : Address) (accounts : AccountMap) : Prop where
  pinned : (accounts.findD self default).code = runtimeBytecode
  locked : (accounts.findD self default).storage.findD ⟨6⟩ ⟨0⟩ ≠ ⟨0⟩
  bounded : worldEth accounts < wordLimit

theorem LockedWorld.next {self before after}
    (initial : LockedWorld self before) (storage : CodeStorageFrame self before after)
    (balances : EthFrame self before after) : LockedWorld self after := by
  refine ⟨storage.2.2.symm.trans (LockedWorld.pinned initial), ?_, balances.1.trans_lt (LockedWorld.bounded initial)⟩
  rw [← storage.1]
  exact (LockedWorld.locked initial)

/-- The opcode obligation at one call depth. -/
def ForeignStepBalances (self : Address) (depth : Fin 1025) : Prop :=
  ∀ (before after : Ethereum.State) gasCost instr,
    before.executionEnv.depth = depth → self ≠ before.executionEnv.codeOwner →
    LockedWorld self before.accountMap → step gasCost instr before = .ok after →
    EthFrame self before.accountMap after.accountMap

/-- Lift opcode balance proofs through validation and environment restoration. -/
theorem foreign_xstep_balances {self : Address} {depth : Fin 1025}
    (steps : ForeignStepBalances self depth)
    {before after : Ethereum.State} {validJumps : Array UInt256} {ret}
    (atDepth : before.executionEnv.depth = depth)
    (foreign : self ≠ before.executionEnv.codeOwner)
    (initial : LockedWorld self before.accountMap)
    (run : Xstep validJumps before = .ok (after, ret)) :
    EthFrame self before.accountMap after.accountMap ∧
      CodeStorageFrame self before.accountMap after.accountMap := by
  set instr : Operation × Option (UInt256 × Nat) :=
    (decode before.executionEnv.code before.machineState.pc).getD (.STOP, .none) with decoded
  rcases instr with ⟨op, arg⟩
  simp [Xstep, ← decoded] at run
  split at run
  · contradiction
  · rename_i checked cost check
    simp [bind, Except.bind] at run
    split at run
    · contradiction
    · rename_i stepped execute
      have check' : Z validJumps op before = .ok (checked, cost) := by
        simpa [← decoded] using check
      have execute' : step cost (op, arg)
          { checked with executionEnv.depth := before.executionEnv.depth } = .ok stepped := by
        simpa [← decoded] using execute
      have accounts := precheck_accounts check'
      have environment := Z_executionEnv_eq check'
      have initial' : LockedWorld self checked.accountMap := by simpa [accounts] using initial
      have foreign' : self ≠
          ({ checked with executionEnv.depth := before.executionEnv.depth } : Ethereum.State).executionEnv.codeOwner := by
        simpa [environment] using foreign
      have balances := steps { checked with executionEnv.depth := before.executionEnv.depth } stepped cost (op, arg) (by exact atDepth) foreign' initial' execute'
      have storage := foreign_step_storage (before := { checked with executionEnv.depth := before.executionEnv.depth }) (run := execute') (LockedWorld.pinned initial') (LockedWorld.locked initial') foreign'
      have result : EthFrame self before.accountMap stepped.accountMap ∧
          CodeStorageFrame self before.accountMap stepped.accountMap := by
        simpa [accounts] using And.intro balances storage
      repeat' first | split at run | contradiction
      all_goals
        have pair := Except.ok.inj run
        have same : { stepped with executionEnv := before.executionEnv } = after :=
          congrArg Prod.fst pair
        rw [← same]
        exact result

/-- Lift opcode balance proofs through any finite successful execution. -/
theorem foreign_x_balances {self : Address} {depth : Fin 1025}
    (steps : ForeignStepBalances self depth)
    {before after : Ethereum.State} {validJumps : Array UInt256} {fuel : Nat} {output}
    (atDepth : before.executionEnv.depth = depth)
    (foreign : self ≠ before.executionEnv.codeOwner)
    (initial : LockedWorld self before.accountMap)
    (run : X fuel validJumps before = .ok (.success after output)) :
    EthFrame self before.accountMap after.accountMap := by
  induction fuel generalizing before with
  | zero => simp [X] at run
  | succ fuel ih =>
    simp only [X] at run
    cases execute : Xstep validJumps before with
    | error err => simp [execute, bind, Except.bind] at run
    | ok pair =>
      rcases pair with ⟨during, ret⟩
      have frames := foreign_xstep_balances steps atDepth foreign initial execute
      have next := initial.next frames.2 frames.1
      have environment := Xstep_env_unchanged before during validJumps ret execute
      rw [execute] at run
      cases ret with
      | none =>
        change X fuel validJumps { during with executionEnv.depth := before.executionEnv.depth } =
          .ok (.success after output) at run
        have tail := ih (before := { during with executionEnv.depth := before.executionEnv.depth }) (by exact atDepth) (by simpa [← environment] using foreign) next run
        exact frames.1.trans tail
      | some result =>
        rcases result with ⟨cause, out⟩
        cases cause with
        | revert => simp [bind, Except.bind] at run
        | success =>
          change Except.ok (ExecutionResult.success during out) =
            Except.ok (ExecutionResult.success after output) at run
          injection run with result
          injection result with same _
          simpa [same] using frames.1

/-- Lift opcode balance proofs to a complete successful code execution. -/
theorem foreign_xi_balances {self : Address}
    {cA gh bl accounts original gas substate env cA' after gas' substate' output}
    (steps : ForeignStepBalances self env.depth)
    (foreign : self ≠ env.codeOwner)
    (initial : LockedWorld self accounts)
    (run : Ξ cA gh bl accounts original gas substate env =
      .ok (.success (cA', after, gas', substate') output)) :
    EthFrame self accounts after := by
  let fresh : Ethereum.State := { (default : Ethereum.State) with
    accountMap := accounts
    σ₀ := original
    executionEnv := env
    substate := substate
    createdAccounts := cA
    machineState.gasAvailable := .ofUInt256 gas
    blocks := bl
    genesisBlockHeader := gh }
  simp only [Ξ, bind, Except.bind] at run
  split at run
  · contradiction
  · rename_i result execute
    cases result with
    | revert gas out => simp at run
    | success finalState out =>
      simp only [Except.ok.injEq, ExecutionResult.success.injEq,
        Prod.mk.injEq] at run
      rcases run with ⟨⟨_, same, _, _⟩, _⟩
      rw [← same]
      exact foreign_x_balances (before := fresh) (after := finalState)
        (fuel := gas.toNat + 1) (validJumps := D_J env.code 0) (output := out)
        steps rfl foreign initial execute

end Rollup.EVM
