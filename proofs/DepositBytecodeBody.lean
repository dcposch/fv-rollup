import proofs.DepositBytecodeGuards

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Rollup.EVM

/-- Load the owner's deposit credit and enter the checked-add routine. -/
theorem deposit_bytecode_load {I : ExecutionEnv} {g : Sat256} {s0 : Ethereum.State}
    {mem : ByteArray} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : Nat}
    (owner : UInt256) (rest : List UInt256) (space : rest.length + 10 ≤ 1024)
    (canonical : owner.toNat < _root_.EVM.addressModulus) (memorySize : mem.size = 96)
    (reached : RD runtimeBytecode I g s0 ⟨1114⟩ (owner :: rest) mem (UInt256.ofNat 3)
      rdata (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g s0 ⟨1385⟩
      (solcSlotWord σ I (solcMappingSlot ⟨4⟩ owner) :: I.weiValue :: ⟨1153⟩ :: ⟨0⟩ ::
        solcMappingSlot ⟨4⟩ owner :: I.weiValue :: owner :: rest)
      (twoWordHashMem owner ⟨4⟩ mem) (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
  have mask : UInt256.sub (UInt256.shiftLeft ⟨1⟩ ⟨160⟩) ⟨1⟩ = solcAddrMask := by decide
  have cleaned := runtime_run reached with [jumpdest, push1 ⟨1⟩, push1 ⟨1⟩,
    push1 ⟨160⟩, shl, sub, dup2, and]
  rw [mask, solcAddrMask_clean canonical] at cleaned
  have beforeOwner := runtime_run cleaned with [push0, swap1, dup2]
  have ownerStored := beforeOwner.mstore 0 (wordAt0Mem owner mem) (UInt256.ofNat 3)
    (by decide +kernel) mem_cost rfl (by decide) (by evm_ov)
  have beforeSlot := runtime_run ownerStored with [push1 ⟨4⟩, push1 ⟨32⟩]
  have slotStored := beforeSlot.mstore 0 (twoWordHashMem owner ⟨4⟩ mem) (UInt256.ofNat 3)
    (by decide +kernel) mem_cost rfl (by decide) (by evm_ov)
  have beforeHash := runtime_run slotStored with [push1 ⟨64⟩, dup2]
  have hashed := beforeHash.keccak256 0 (solcMappingSlot ⟨4⟩ owner) (UInt256.ofNat 3)
    (by decide +kernel) mem_cost (twoWordHashMem_solcMappingSlot ⟨4⟩ owner memorySize)
    (by decide) (by evm_ov)
  have saved := runtime_run hashed with [dup1]
  obtain ⟨_, _, loaded⟩ := saved.sload (by decide +kernel) (by evm_ov)
  exact ⟨_, _, runtime_run loaded with [callvalue, swap3, swap1, push2 ⟨1153⟩,
    swap1, dup5, swap1, push2 ⟨1385⟩,
    jump (jumpScan_valid runtimeBytecode 1385 1400 (by decide +kernel))]⟩

/-- The add routine returns the sum when it fits in one word. -/
theorem runtime_checked_add {I : ExecutionEnv} {g : Sat256} {s0 : Ethereum.State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (a b ret : UInt256) (rest : List UInt256) (space : rest.length + 6 ≤ 1024)
    (fits : a.toNat + b.toNat < UInt256.size)
    (destination : (D_J runtimeBytecode 0).contains ret = true)
    (reached : RD runtimeBytecode I g s0 ⟨1385⟩ (b :: a :: ret :: rest)
      mem aw rdata acc k C) :
    ∃ k' C', RD runtimeBytecode I g s0 ret ((a + b) :: rest) mem aw rdata acc k' C' := by
  have sumNat : (a + b).toNat = a.toNat + b.toNat := by
    rw [uadd_toNat, Nat.mod_eq_of_lt fits]
  have compare : UInt256.gt b (a + b) = ⟨0⟩ := ugt_zero (by rw [sumNat]; omega)
  have checked := runtime_run reached with [jumpdest, dup1, dup3, add, dup1, dup3,
    gt, iszero, push2 ⟨1404⟩]
  rw [compare] at checked
  exact ⟨_, _, runtime_run checked with [
    jumpiT (by decide) (jumpScan_valid runtimeBytecode 1404 1420 (by decide +kernel)),
    jumpdest, swap3, swap2, pop, pop, jump destination]⟩

/-- Store the new credit, release the lock, and return to the dispatcher. -/
theorem deposit_bytecode_store {I : ExecutionEnv} {g : Sat256} {s0 : Ethereum.State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : Nat}
    (credit slot value owner ret : UInt256) (rest : List UInt256)
    (space : rest.length + 6 ≤ 1024) (writable : I.perm = true)
    (destination : (D_J runtimeBytecode 0).contains ret = true)
    (reached : RD runtimeBytecode I g s0 ⟨1153⟩
      (credit :: ⟨0⟩ :: slot :: value :: owner :: ret :: rest) mem aw rdata (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g s0 ret rest mem aw rdata
      (cA, sstoreAccountMap I.codeOwner (sstoreAccountMap I.codeOwner σ slot credit) ⟨6⟩ ⟨0⟩)
      k' C' := by
  have beforeCredit := runtime_run reached with [jumpdest, swap1, swap2]
  obtain ⟨_, _, stored⟩ := beforeCredit.sstore writable (by decide +kernel) (by evm_ov)
  have beforeUnlock := runtime_run stored with [pop, pop, push0, push1 ⟨6⟩]
  obtain ⟨_, _, unlocked⟩ := beforeUnlock.sstore writable (by decide +kernel) (by evm_ov)
  exact ⟨_, _, runtime_run unlocked with [pop, jump destination]⟩

end Rollup.EVM
