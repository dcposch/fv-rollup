import proofs.DepositWitness
import proofs.DepositBytecodeSuccess

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Rollup.EVM

theorem deposit_mapping_slot_one : solcMappingSlot ⟨4⟩ ⟨1⟩ =
    ⟨0xabd6e7cb50984ff9c2f3e18a2660c3353dadf4e3291deeb275dae2cd1e44fe05⟩ := by
  unfold solcMappingSlot
  have input : (⟨1⟩ : UInt256).toByteArray ++ (⟨4⟩ : UInt256).toByteArray = ⟨#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4]⟩ := by
    keccak_cbv
  rw [input, HashCertificates.deposit_mapping_one]
  decide +kernel

/-- A one-wei deposit succeeds, stores its credit, and releases the lock. -/
theorem deposit_success_witness :
    ∃ accounts gas substate,
      Ξ default default default DepositWitness.witnessStart.accountMap default
        ⟨1000000⟩ default DepositWitness.witnessEnv =
        .ok (.success (default, accounts, gas, substate) ByteArray.empty) ∧
      solcSlotWord accounts DepositWitness.witnessEnv
        (solcMappingSlot ⟨4⟩ ⟨1⟩) = ⟨1⟩ ∧
      solcSlotWord accounts DepositWitness.witnessEnv ⟨6⟩ = ⟨0⟩ ∧
      (accounts.find? 42).map (·.balance) = some ⟨1⟩ := by
  obtain ⟨final, output, executed, empty⟩ := DepositWitness.executes
  have success := Xi_success_of_X
    (createdAccounts := default) (genesisBlockHeader := default) (blocks := default)
    (σ := DepositWitness.witnessStart.accountMap) (σ₀ := default) (A := default)
    (I := DepositWitness.witnessEnv) (g := ⟨1000000⟩) (by exact executed)
  obtain ⟨_, _, _, _, _, _, _, _, created, accounts, outputEq⟩ :=
    deposit_xi_success (I := DepositWitness.witnessEnv)
      rfl rfl (by decide +kernel) (by decide +kernel) success
  have decoded : calldataWord DepositWitness.witnessEnv.calldata 4 = ⟨1⟩ := by
    decide +kernel
  rw [decoded] at accounts
  rw [created, outputEq] at success
  refine ⟨final.accountMap, final.machineState.gasAvailable.toUInt256,
    final.substate, success, ?_⟩
  rw [accounts, deposit_mapping_slot_one]
  decide +kernel

end Rollup.EVM
