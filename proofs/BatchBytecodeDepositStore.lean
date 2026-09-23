import proofs.BatchBytecodeDeposit

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Rollup.EVM

def batchDepositWrite (accounts : AccountMap) (I : ExecutionEnv) (credit : UInt256) : AccountMap :=
  sstoreAccountMap I.codeOwner accounts (batchDepositSlot I)
    (UInt256.sub credit (calldataWord I.calldata 132))

/-- Debit deposit credit, then load backing and enter checked addition. -/
theorem batch_bytecode_deposit_store {I : ExecutionEnv} {g : Sat256} {s0 : Ethereum.State}
    {mem : ByteArray} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : Nat}
    (credit : UInt256) (rest : List UInt256) (space : rest.length + 13 ≤ 1024)
    (writable : I.perm = true)
    (canonical : (calldataWord I.calldata 100).toNat < _root_.EVM.addressModulus)
    (memorySize : mem.size = 96)
    (reached : RD runtimeBytecode I g s0 ⟨706⟩
      (UInt256.sub credit (calldataWord I.calldata 132) :: credit :: batchDecodedStack I rest)
      mem (UInt256.ofNat 3) rdata (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g s0 ⟨1385⟩
      (solcSlotWord (batchDepositWrite σ I credit) I ⟨3⟩ :: calldataWord I.calldata 132 ::
        ⟨747⟩ :: ⟨0⟩ :: credit :: batchDecodedStack I rest)
      (twoWordHashMem (calldataWord I.calldata 100) ⟨4⟩ mem) (UInt256.ofNat 3) rdata
      (cA, batchDepositWrite σ I credit) k' C' := by
  dsimp only [batchDecodedStack] at reached
  have mask : UInt256.sub (UInt256.shiftLeft ⟨1⟩ ⟨160⟩) ⟨1⟩ = solcAddrMask := by decide
  have cleaned := runtime_run reached with [jumpdest, push1 ⟨1⟩, push1 ⟨1⟩,
    push1 ⟨160⟩, shl, sub, dup7, and]
  rw [mask, solcAddrMask_clean canonical] at cleaned
  have beforeOwner := runtime_run cleaned with [push0, swap1, dup2]
  have ownerStored := beforeOwner.mstore 0 (wordAt0Mem (calldataWord I.calldata 100) mem) (UInt256.ofNat 3)
    (by decide +kernel) mem_cost rfl (by decide) (by evm_ov)
  have beforeSlot := runtime_run ownerStored with [push1 ⟨4⟩, push1 ⟨32⟩]
  have slotStored := beforeSlot.mstore 0 (twoWordHashMem (calldataWord I.calldata 100) ⟨4⟩ mem)
    (UInt256.ofNat 3) (by decide +kernel) mem_cost rfl (by decide) (by evm_ov)
  have beforeHash := runtime_run slotStored with [push1 ⟨64⟩, dup2]
  have hashed := beforeHash.keccak256 0 (batchDepositSlot I) (UInt256.ofNat 3)
    (by decide +kernel) mem_cost (twoWordHashMem_solcMappingSlot ⟨4⟩ _ memorySize)
    (by decide) (by evm_ov)
  have beforeDebit := runtime_run hashed with [swap2, swap1, swap2]
  obtain ⟨_, _, debited⟩ := beforeDebit.sstore writable (by decide +kernel) (by evm_ov)
  have backingSlot := runtime_run debited with [push1 ⟨3⟩]
  obtain ⟨_, _, backingLoaded⟩ := backingSlot.sload (by decide +kernel) (by evm_ov)
  exact ⟨_, _, runtime_run backingLoaded with [push2 ⟨747⟩, swap1, dup7, swap1,
    push2 ⟨1385⟩, jump (jumpScan_valid runtimeBytecode 1385 1400 (by decide +kernel))]⟩

end Rollup.EVM
