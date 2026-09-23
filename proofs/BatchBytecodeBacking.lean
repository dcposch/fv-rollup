import proofs.BatchEntry
import proofs.RuntimeSubtract

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Rollup.EVM

def batchClaimSlot (I : ExecutionEnv) : UInt256 :=
  solcMappingSlot ⟨5⟩ (calldataWord I.calldata 164)

def batchBackingWrite (accounts : AccountMap) (I : ExecutionEnv) (available : UInt256) : AccountMap :=
  sstoreAccountMap I.codeOwner accounts ⟨3⟩ (UInt256.sub available (calldataWord I.calldata 196))

/-- A batch cannot allocate more withdrawal credit than its available backing. -/
theorem batch_bytecode_backing_check_cases {I : ExecutionEnv} {g : Sat256} {s0 : Ethereum.State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (available credit : UInt256) (rest : List UInt256) (space : rest.length + 15 ≤ 1024)
    (reached : RD runtimeBytecode I g s0 ⟨747⟩ (available :: ⟨0⟩ :: credit :: batchDecodedStack I rest)
      mem aw rdata acc k C) :
    (RDrev runtimeBytecode g s0 ∧ ¬((calldataWord I.calldata 196).toNat ≤ available.toNat)) ∨
      ((calldataWord I.calldata 196).toNat ≤ available.toNat ∧
       ∃ k' C', RD runtimeBytecode I g s0 ⟨771⟩
         (UInt256.sub available (calldataWord I.calldata 196) :: available :: credit :: batchDecodedStack I rest)
         mem aw rdata acc k' C') := by
  dsimp only [batchDecodedStack] at reached
  have guard := runtime_run reached with [jumpdest, swap1, pop, dup1, dup4, gt, iszero, push2 ⟨761⟩]
  by_cases covered : (calldataWord I.calldata 196).toNat ≤ available.toNat
  · have subEntry := runtime_run guard with [jumpiT (by rw [ugt_zero covered]; decide)
      (jumpScan_valid runtimeBytecode 761 790 (by decide +kernel)),
      jumpdest, push2 ⟨771⟩, dup4, dup3, push2 ⟨1410⟩,
      jump (jumpScan_valid runtimeBytecode 1410 1430 (by decide +kernel))]
    exact Or.inr ⟨covered, runtime_checked_subtract available (calldataWord I.calldata 196) ⟨771⟩
      (available :: credit :: batchDecodedStack I rest)
      (by simp only [batchDecodedStack, List.length_cons]; omega)
      covered (jumpScan_valid runtimeBytecode 771 800 (by decide +kernel)) subEntry⟩
  · have tooLarge : UInt256.gt (calldataWord I.calldata 196) available = ⟨1⟩ := ugt_one (by omega)
    have rejected := runtime_run guard with [jumpiNT (by rw [tooLarge]; decide), push0, dup1]
    exact Or.inl ⟨(rejected.rev 0 (by decide +kernel)
      (fun s _ items => memExpRevert0 s items) (by evm_ov)), by exact covered⟩

/-- Discard the reason for rejection. -/
theorem batch_bytecode_backing_check {I : ExecutionEnv} {g : Sat256} {s0 : Ethereum.State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (available credit : UInt256) (rest : List UInt256) (space : rest.length + 15 ≤ 1024)
    (reached : RD runtimeBytecode I g s0 ⟨747⟩ (available :: ⟨0⟩ :: credit :: batchDecodedStack I rest)
      mem aw rdata acc k C) :
    RDrev runtimeBytecode g s0 ∨
      ((calldataWord I.calldata 196).toNat ≤ available.toNat ∧
       ∃ k' C', RD runtimeBytecode I g s0 ⟨771⟩
         (UInt256.sub available (calldataWord I.calldata 196) :: available :: credit :: batchDecodedStack I rest)
         mem aw rdata acc k' C') := by
  rcases batch_bytecode_backing_check_cases available credit rest space reached with ⟨rejected, _⟩ | accepted
  · exact Or.inl rejected
  · exact Or.inr accepted

/-- Store backing, then load withdrawal credit and enter checked addition. -/
theorem batch_bytecode_backing_store {I : ExecutionEnv} {g : Sat256} {s0 : Ethereum.State}
    {mem : ByteArray} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : Nat}
    (available credit : UInt256) (rest : List UInt256) (space : rest.length + 16 ≤ 1024)
    (writable : I.perm = true)
    (canonical : (calldataWord I.calldata 164).toNat < _root_.EVM.addressModulus)
    (memorySize : mem.size = 96)
    (reached : RD runtimeBytecode I g s0 ⟨771⟩
      (UInt256.sub available (calldataWord I.calldata 196) :: available :: credit :: batchDecodedStack I rest)
      mem (UInt256.ofNat 3) rdata (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g s0 ⟨1385⟩
      (solcSlotWord (batchBackingWrite σ I available) I (batchClaimSlot I) ::
        calldataWord I.calldata 196 :: ⟨813⟩ :: ⟨0⟩ :: batchClaimSlot I ::
        calldataWord I.calldata 196 :: available :: credit :: batchDecodedStack I rest)
      (twoWordHashMem (calldataWord I.calldata 164) ⟨5⟩ mem) (UInt256.ofNat 3) rdata
      (cA, batchBackingWrite σ I available) k' C' := by
  dsimp only [batchDecodedStack] at reached
  have beforeBacking := runtime_run reached with [jumpdest, push1 ⟨3⟩]
  obtain ⟨_, _, backed⟩ := beforeBacking.sstore writable (by decide +kernel) (by evm_ov)
  have mask : UInt256.sub (UInt256.shiftLeft ⟨1⟩ ⟨160⟩) ⟨1⟩ = solcAddrMask := by decide
  have cleaned := runtime_run backed with [push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup5, and]
  rw [mask, solcAddrMask_clean canonical] at cleaned
  have beforeOwner := runtime_run cleaned with [push0, swap1, dup2]
  have ownerStored := beforeOwner.mstore 0 (wordAt0Mem (calldataWord I.calldata 164) mem) (UInt256.ofNat 3)
    (by decide +kernel) mem_cost rfl (by decide) (by evm_ov)
  have beforeSlot := runtime_run ownerStored with [push1 ⟨5⟩, push1 ⟨32⟩]
  have slotStored := beforeSlot.mstore 0 (twoWordHashMem (calldataWord I.calldata 164) ⟨5⟩ mem)
    (UInt256.ofNat 3) (by decide +kernel) mem_cost rfl (by decide) (by evm_ov)
  have beforeHash := runtime_run slotStored with [push1 ⟨64⟩, dup2]
  have hashed := beforeHash.keccak256 0 (batchClaimSlot I) (UInt256.ofNat 3)
    (by decide +kernel) mem_cost (twoWordHashMem_solcMappingSlot ⟨5⟩ _ memorySize)
    (by decide) (by evm_ov)
  have beforeCredit := runtime_run hashed with [dup1]
  obtain ⟨_, _, creditLoaded⟩ := beforeCredit.sload (by decide +kernel) (by evm_ov)
  exact ⟨_, _, runtime_run creditLoaded with [dup6, swap3, swap1, push2 ⟨813⟩, swap1, dup5, swap1,
    push2 ⟨1385⟩, jump (jumpScan_valid runtimeBytecode 1385 1400 (by decide +kernel))]⟩

end Rollup.EVM
