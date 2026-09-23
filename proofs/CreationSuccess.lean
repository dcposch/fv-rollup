import proofs.CreationWitness

open Ethereum Ethereum.EVM Reasoning.Theory

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Rollup.EVM

noncomputable def creationWitnessAccounts : AccountMap :=
  (default : AccountMap).insert 42 { (default : Account) with nonce := ⟨1⟩ }

/-- A fresh constructor run returns the pinned code and can pay the code-deposit cost. -/
theorem creation_success_witness :
    ∃ gas substate,
      Ξ default default default creationWitnessAccounts default ⟨1000000⟩ default
        CreationWitness.witnessEnv =
        .ok (.success (default,
          sstoreAccountMap 42 (sstoreAccountMap 42 creationWitnessAccounts ⟨0⟩ ⟨1⟩)
            ⟨1⟩ ⟨1⟩, gas, substate) runtimeBytecode) ∧
      285800 ≤ gas.toNat := by
  obtain ⟨final, output, executed, enough⟩ := CreationWitness.executes
  have success := Xi_success_of_X
    (createdAccounts := default) (genesisBlockHeader := default) (blocks := default)
    (σ := creationWitnessAccounts) (σ₀ := default) (A := default)
    (I := CreationWitness.witnessEnv) (g := ⟨1000000⟩) (by exact executed)
  have classified := creation_xi_result
    (cA := default) (gh := default) (bl := default)
    (σ := creationWitnessAccounts) (σ₀ := default) (A := default)
    (I := CreationWitness.witnessEnv) (g := ⟨1000000⟩)
    ⟨1⟩ ⟨1⟩ (by decide) (by decide) rfl rfl
    (by decide +kernel) (by
      change creationBytecode ++ _ = creationBytecode ++ _
      apply congrArg (creationBytecode ++ ·)
      decide +kernel)
  rcases classified with failed | ⟨gas, substate, result⟩
  · rw [failed] at success
    cases success
  · refine ⟨gas, substate, result, ?_⟩
    have gasEq : gas = final.machineState.gasAvailable.toUInt256 := by
      have same := result.symm.trans success
      injection same with same
      injection same with accountsEq outputEq
      exact congrArg (fun item => item.2.2.1) accountsEq
    rw [gasEq]
    exact enough

end Rollup.EVM
