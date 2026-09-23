import proofs.BatchBytecodeAuthorization
import proofs.DepositBytecodeBody
import proofs.RuntimeOverflow

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Rollup.EVM

/-- The batch header checks the next number and the old root. -/
theorem batch_bytecode_header_cases {I : ExecutionEnv} {g : Sat256} {s0 : Ethereum.State}
    {mem : ByteArray} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : Nat}
    (rest : List UInt256) (space : rest.length + 15 ≤ 1024)
    (reached : RD runtimeBytecode I g s0 ⟨479⟩ (batchDecodedStack I rest)
      mem (UInt256.ofNat 3) rdata (cA, σ) k C) :
    (RDrev runtimeBytecode g s0 ∧ ¬((solcSlotWord σ I ⟨2⟩).toNat + 1 < UInt256.size ∧
       calldataWord I.calldata 4 = solcSlotWord σ I ⟨2⟩ + ⟨1⟩ ∧
       calldataWord I.calldata 36 = solcSlotWord σ I ⟨1⟩)) ∨
      ((solcSlotWord σ I ⟨2⟩).toNat + 1 < UInt256.size ∧
       calldataWord I.calldata 4 = solcSlotWord σ I ⟨2⟩ + ⟨1⟩ ∧
       calldataWord I.calldata 36 = solcSlotWord σ I ⟨1⟩ ∧
       ∃ k' C', RD runtimeBytecode I g s0 ⟨516⟩ (batchDecodedStack I rest)
         mem (UInt256.ofNat 3) rdata (cA, σ) k' C') := by
  dsimp only [batchDecodedStack] at reached
  have slot := runtime_run reached with [jumpdest, push1 ⟨2⟩]
  obtain ⟨_, _, loaded⟩ := slot.sload (by decide +kernel) (by evm_ov)
  have addEntry := runtime_run loaded with [push2 ⟨493⟩, swap1, push1 ⟨1⟩,
    push2 ⟨1385⟩, jump (jumpScan_valid runtimeBytecode 1385 1400 (by decide +kernel))]
  by_cases fits : (solcSlotWord σ I ⟨2⟩).toNat + 1 < UInt256.size
  · obtain ⟨_, _, added⟩ := runtime_checked_add (solcSlotWord σ I ⟨2⟩) ⟨1⟩ ⟨493⟩
      (batchDecodedStack I rest) (by simp only [batchDecodedStack, List.length_cons]; omega)
      fits (jumpScan_valid runtimeBytecode 493 520 (by decide +kernel)) addEntry
    dsimp only [batchDecodedStack] at added
    have numberGuard := runtime_run added with [jumpdest, dup8, eq, push2 ⟨503⟩]
    by_cases number : calldataWord I.calldata 4 = solcSlotWord σ I ⟨2⟩ + ⟨1⟩
    · rw [number, u256_eq_refl] at numberGuard
      have rootSlot := runtime_run numberGuard with [jumpiT (by decide)
        (jumpScan_valid runtimeBytecode 503 530 (by decide +kernel)), jumpdest, push1 ⟨1⟩]
      obtain ⟨_, _, rootLoaded⟩ := rootSlot.sload (by decide +kernel) (by evm_ov)
      have rootGuard := runtime_run rootLoaded with [dup7, eq, push2 ⟨516⟩]
      by_cases root : calldataWord I.calldata 36 = solcSlotWord σ I ⟨1⟩
      · rw [root, u256_eq_refl] at rootGuard
        have accepted := runtime_run rootGuard with [jumpiT (by decide)
          (jumpScan_valid runtimeBytecode 516 550 (by decide +kernel))]
        rw [← number, ← root] at accepted
        exact Or.inr ⟨fits, number, root, _, _, accepted⟩
      · rw [u256_eq_of_ne root] at rootGuard
        have rejected := runtime_run rootGuard with [jumpiNT rfl, push0, dup1]
        exact Or.inl ⟨(rejected.rev 0 (by decide +kernel)
          (fun s _ items => memExpRevert0 s items) (by evm_ov)), by intro checks; exact root checks.2.2⟩
    · rw [u256_eq_of_ne number] at numberGuard
      have rejected := runtime_run numberGuard with [jumpiNT rfl, push0, dup1]
      exact Or.inl ⟨(rejected.rev 0 (by decide +kernel)
        (fun s _ items => memExpRevert0 s items) (by evm_ov)), by intro checks; exact number checks.2.1⟩
  · exact Or.inl ⟨(runtime_checked_add_overflow (solcSlotWord σ I ⟨2⟩) ⟨1⟩ ⟨493⟩
      (batchDecodedStack I rest) (by simp only [batchDecodedStack, List.length_cons]; omega)
      (by simpa using Nat.le_of_not_lt fits) addEntry), by intro checks; exact fits checks.1⟩

/-- Discard the reason for rejection. -/
theorem batch_bytecode_header {I : ExecutionEnv} {g : Sat256} {s0 : Ethereum.State}
    {mem : ByteArray} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : Nat}
    (rest : List UInt256) (space : rest.length + 15 ≤ 1024)
    (reached : RD runtimeBytecode I g s0 ⟨479⟩ (batchDecodedStack I rest)
      mem (UInt256.ofNat 3) rdata (cA, σ) k C) :
    RDrev runtimeBytecode g s0 ∨
      ((solcSlotWord σ I ⟨2⟩).toNat + 1 < UInt256.size ∧
       calldataWord I.calldata 4 = solcSlotWord σ I ⟨2⟩ + ⟨1⟩ ∧
       calldataWord I.calldata 36 = solcSlotWord σ I ⟨1⟩ ∧
       ∃ k' C', RD runtimeBytecode I g s0 ⟨516⟩ (batchDecodedStack I rest)
         mem (UInt256.ofNat 3) rdata (cA, σ) k' C') := by
  rcases batch_bytecode_header_cases rest space reached with ⟨rejected, _⟩ | accepted
  · exact Or.inl rejected
  · exact Or.inr accepted

end Rollup.EVM
