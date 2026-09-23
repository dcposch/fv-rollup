import proofs.BatchEntry
import proofs.RuntimeSubtract

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Rollup.EVM

def batchDepositSlot (I : ExecutionEnv) : UInt256 :=
  solcMappingSlot ⟨4⟩ (calldataWord I.calldata 100)

def batchDepositWord (accounts : AccountMap) (I : ExecutionEnv) : UInt256 :=
  solcSlotWord accounts I (batchDepositSlot I)

/-- Load the deposit credit from the checked owner's mapping slot. -/
theorem batch_bytecode_deposit_load {I : ExecutionEnv} {g : Sat256} {s0 : Ethereum.State}
    {mem : ByteArray} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : Nat}
    (rest : List UInt256) (space : rest.length + 11 ≤ 1024)
    (canonical : (calldataWord I.calldata 100).toNat < _root_.EVM.addressModulus)
    (memorySize : mem.size = 96)
    (reached : RD runtimeBytecode I g s0 ⟨660⟩ (batchDecodedStack I rest)
      mem (UInt256.ofNat 3) rdata (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g s0 ⟨685⟩
      (batchDepositWord σ I :: batchDecodedStack I rest)
      (twoWordHashMem (calldataWord I.calldata 100) ⟨4⟩ mem) (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
  dsimp only [batchDecodedStack] at reached
  have mask : UInt256.sub (UInt256.shiftLeft ⟨1⟩ ⟨160⟩) ⟨1⟩ = solcAddrMask := by decide
  have cleaned := runtime_run reached with [jumpdest, push1 ⟨1⟩, push1 ⟨1⟩,
    push1 ⟨160⟩, shl, sub, dup5, and]
  rw [mask, solcAddrMask_clean canonical] at cleaned
  have beforeOwner := runtime_run cleaned with [push0, swap1, dup2]
  have ownerStored := beforeOwner.mstore 0 (wordAt0Mem (calldataWord I.calldata 100) mem) (UInt256.ofNat 3)
    (by decide +kernel) mem_cost rfl (by decide) (by evm_ov)
  have beforeSlot := runtime_run ownerStored with [push1 ⟨4⟩, push1 ⟨32⟩]
  have slotStored := beforeSlot.mstore 0 (twoWordHashMem (calldataWord I.calldata 100) ⟨4⟩ mem)
    (UInt256.ofNat 3) (by decide +kernel) mem_cost rfl (by decide) (by evm_ov)
  have beforeHash := runtime_run slotStored with [push1 ⟨64⟩, swap1]
  have hashed := beforeHash.keccak256 0 (batchDepositSlot I) (UInt256.ofNat 3)
    (by decide +kernel) mem_cost (twoWordHashMem_solcMappingSlot ⟨4⟩ _ memorySize)
    (by decide) (by evm_ov)
  exact hashed.sload (by decide +kernel) (by evm_ov)

/-- A batch cannot consume more than its deposit credit. -/
theorem batch_bytecode_deposit_check_cases {I : ExecutionEnv} {g : Sat256} {s0 : Ethereum.State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (credit : UInt256) (rest : List UInt256) (space : rest.length + 14 ≤ 1024)
    (reached : RD runtimeBytecode I g s0 ⟨685⟩ (credit :: batchDecodedStack I rest)
      mem aw rdata acc k C) :
    (RDrev runtimeBytecode g s0 ∧ ¬((calldataWord I.calldata 132).toNat ≤ credit.toNat)) ∨
      ((calldataWord I.calldata 132).toNat ≤ credit.toNat ∧
       ∃ k' C', RD runtimeBytecode I g s0 ⟨706⟩
         (UInt256.sub credit (calldataWord I.calldata 132) :: credit :: batchDecodedStack I rest)
         mem aw rdata acc k' C') := by
  dsimp only [batchDecodedStack] at reached
  have guard := runtime_run reached with [dup1, dup5, gt, iszero, push2 ⟨696⟩]
  by_cases covered : (calldataWord I.calldata 132).toNat ≤ credit.toNat
  · have subEntry := runtime_run guard with [jumpiT (by rw [ugt_zero covered]; decide)
      (jumpScan_valid runtimeBytecode 696 720 (by decide +kernel)),
      jumpdest, push2 ⟨706⟩, dup5, dup3, push2 ⟨1410⟩,
      jump (jumpScan_valid runtimeBytecode 1410 1430 (by decide +kernel))]
    exact Or.inr ⟨covered, runtime_checked_subtract credit (calldataWord I.calldata 132) ⟨706⟩
      (credit :: batchDecodedStack I rest) (by simp only [batchDecodedStack, List.length_cons]; omega)
      covered (jumpScan_valid runtimeBytecode 706 735 (by decide +kernel)) subEntry⟩
  · have tooLarge : UInt256.gt (calldataWord I.calldata 132) credit = ⟨1⟩ := ugt_one (by omega)
    have rejected := runtime_run guard with [jumpiNT (by rw [tooLarge]; decide), push0, dup1]
    exact Or.inl ⟨(rejected.rev 0 (by decide +kernel)
      (fun s _ items => memExpRevert0 s items) (by evm_ov)), by exact covered⟩

/-- Discard the reason for rejection. -/
theorem batch_bytecode_deposit_check {I : ExecutionEnv} {g : Sat256} {s0 : Ethereum.State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (credit : UInt256) (rest : List UInt256) (space : rest.length + 14 ≤ 1024)
    (reached : RD runtimeBytecode I g s0 ⟨685⟩ (credit :: batchDecodedStack I rest)
      mem aw rdata acc k C) :
    RDrev runtimeBytecode g s0 ∨
      ((calldataWord I.calldata 132).toNat ≤ credit.toNat ∧
       ∃ k' C', RD runtimeBytecode I g s0 ⟨706⟩
         (UInt256.sub credit (calldataWord I.calldata 132) :: credit :: batchDecodedStack I rest)
         mem aw rdata acc k' C') := by
  rcases batch_bytecode_deposit_check_cases credit rest space reached with ⟨rejected, _⟩ | accepted
  · exact Or.inl rejected
  · exact Or.inr accepted

end Rollup.EVM
