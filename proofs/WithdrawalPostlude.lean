import proofs.WithdrawalReturnData
import proofs.RuntimeSubtract

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Rollup.EVM

-- General scratch-memory lemmas adapted from EquiVM's Flopper/AuctionCommon.
private theorem twoWordHashMem_size_ge_64 (key slot : UInt256) (mem : ByteArray) :
    64 ≤ (twoWordHashMem key slot mem).size := by
  have hkeySize : 32 ≤ (wordAt0Mem key mem).size := by
    unfold wordAt0Mem
    simpa using
      toByteArray_write_size_ge_off_add32 key mem 0 (by simp)
  unfold twoWordHashMem wordAt32Mem
  simpa using
    toByteArray_write_size_ge_off_add32 slot (wordAt0Mem key mem) 32 (by
      have hzero : 32 - (wordAt0Mem key mem).size = 0 := by omega
      rw [hzero]
      exact lt_usize 0 (by norm_num))

private theorem twoWordHashMem_read0_any (key slot : UInt256) (mem : ByteArray) :
    (twoWordHashMem key slot mem).readWithPadding 0 32 =
      UInt256.toByteArray key := by
  have hkeySize : 32 ≤ (wordAt0Mem key mem).size := by
    unfold wordAt0Mem
    simpa using
      toByteArray_write_size_ge_off_add32 key mem 0 (by simp)
  unfold twoWordHashMem wordAt32Mem
  rw [write32_read_below _ _ 32 0 (by rw [toByteArray_size]) hkeySize (by omega)]
  exact wordAt0Mem_read0 key mem

private theorem twoWordHashMem_read32_any (key slot : UInt256) (mem : ByteArray) :
    (twoWordHashMem key slot mem).readWithPadding 32 32 =
      UInt256.toByteArray slot := by
  have hkeySize : 32 ≤ (wordAt0Mem key mem).size := by
    unfold wordAt0Mem
    simpa using
      toByteArray_write_size_ge_off_add32 key mem 0 (by simp)
  unfold twoWordHashMem wordAt32Mem
  exact toByteArray_write32_read_back (wordAt0Mem key mem) slot 32 hkeySize

private theorem twoWordHashMem_read0_64_any (key slot : UInt256) (mem : ByteArray) :
    (twoWordHashMem key slot mem).readWithPadding 0 64 =
      UInt256.toByteArray key ++ UInt256.toByteArray slot := by
  rw [byteArray_readWithPadding_split (twoWordHashMem key slot mem) 0 32 32
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by simpa using twoWordHashMem_size_ge_64 key slot mem)]
  rw [twoWordHashMem_read0_any, twoWordHashMem_read32_any]

private theorem twoWordHashMem_solcMappingSlot_any (baseSlot key : UInt256) (mem : ByteArray) :
    UInt256.ofNat (fromByteArrayBigEndian
        (Ethereum.KEC ((twoWordHashMem key baseSlot mem).readWithPadding 0 64))) =
      solcMappingSlot baseSlot key := by
  rw [twoWordHashMem_read0_64_any]
  unfold solcMappingSlot
  exact mappingSlot_single key baseSlot

/-- A failed payment rejects. A successful payment enters the debit path. -/
theorem withdrawal_bytecode_payment_check {I : ExecutionEnv} {g : Sat256} {s0 : Ethereum.State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (status credit amount owner : UInt256) (rest : List UInt256) (space : rest.length + 6 ≤ 1024)
    (reached : RD runtimeBytecode I g s0 ⟨991⟩ (status :: credit :: amount :: owner :: rest)
      mem aw rdata acc k C) :
    (RDrev runtimeBytecode g s0 ∧ status = ⟨0⟩) ∨
      (status ≠ ⟨0⟩ ∧ ∃ k' C', RD runtimeBytecode I g s0 ⟨999⟩
        (status :: credit :: amount :: owner :: rest) mem aw rdata acc k' C') := by
  have guard := runtime_run reached with [dup1, push2 ⟨999⟩]
  by_cases zero : status = ⟨0⟩
  · have rejected := runtime_run guard with [jumpiNT zero, push0, dup1]
    exact .inl ⟨rejected.rev 0 (by decide +kernel)
      (fun s _ items => memExpRevert0 s items) (by evm_ov), zero⟩
  · exact .inr ⟨zero, _, _, runtime_run guard with [jumpiT zero
      (jumpScan_valid runtimeBytecode 999 1020 (by decide +kernel))]⟩

/-- Debit the saved credit, release the lock, and return to the caller. -/
theorem withdrawal_bytecode_debit {I : ExecutionEnv} {g : Sat256} {s0 : Ethereum.State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : Nat}
    (status credit amount owner ret : UInt256) (rest : List UInt256)
    (space : rest.length + 16 ≤ 1024)
    (writable : I.perm = true)
    (canonical : owner.toNat < _root_.EVM.addressModulus)
    (covered : amount.toNat ≤ credit.toNat)
    (destination : (D_J runtimeBytecode 0).contains ret = true)
    (reached : RD runtimeBytecode I g s0 ⟨999⟩
      (status :: credit :: amount :: owner :: ret :: rest) mem aw rdata (cA, σ) k C) :
    ∃ mem' aw' k' C', RD runtimeBytecode I g s0 ret rest mem' aw' rdata
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σ (solcMappingSlot ⟨5⟩ owner) (UInt256.sub credit amount))
        ⟨6⟩ ⟨0⟩) k' C' := by
  have beforeSub := runtime_run reached with [jumpdest, push2 ⟨1009⟩, dup4, dup4,
    push2 ⟨1410⟩, jump (jumpScan_valid runtimeBytecode 1410 1430 (by decide +kernel))]
  obtain ⟨_, _, subtracted⟩ := runtime_checked_subtract credit amount ⟨1009⟩
    (status :: credit :: amount :: owner :: ret :: rest) (by simp; omega) covered
    (jumpScan_valid runtimeBytecode 1009 1030 (by decide +kernel)) beforeSub
  have mask : UInt256.sub (UInt256.shiftLeft ⟨1⟩ ⟨160⟩) ⟨1⟩ = solcAddrMask := by decide
  have cleaned := runtime_run subtracted with [jumpdest, push1 ⟨1⟩, push1 ⟨1⟩,
    push1 ⟨160⟩, shl, sub, swap1, swap5, and]
  rw [mask, solcAddrMask_clean canonical] at cleaned
  have beforeOwner := runtime_run cleaned with [push0, swap1, dup2]
  let aw0 := UInt256.ofNat (MachineState.M aw.toNat 0 32)
  have ownerStored := beforeOwner.mstore (Cₘ aw0 - Cₘ aw) (wordAt0Mem owner mem) aw0
    (by decide +kernel)
    (by intro s words stack; simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', words, stack,
        List.getElem!_cons_zero]; rfl)
    rfl rfl (by evm_ov)
  have beforeSlot := runtime_run ownerStored with [push1 ⟨5⟩, push1 ⟨32⟩]
  let aw32 := UInt256.ofNat (MachineState.M aw0.toNat 32 32)
  have slotStored := beforeSlot.mstore (Cₘ aw32 - Cₘ aw0) (twoWordHashMem owner ⟨5⟩ mem) aw32
    (by decide +kernel)
    (by intro s words stack; simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', words, stack,
        List.getElem!_cons_zero]; rfl)
    rfl rfl (by evm_ov)
  have beforeHash := runtime_run slotStored with [push1 ⟨64⟩, dup2]
  let awHash := UInt256.ofNat (MachineState.M aw32.toNat 0 64)
  have hashed := beforeHash.keccak256 (Cₘ awHash - Cₘ aw32) (solcMappingSlot ⟨5⟩ owner) awHash
    (by decide +kernel)
    (by intro s words stack; simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', words, stack,
        List.getElem!_cons_zero, List.getElem!_cons_succ]; rfl)
    (twoWordHashMem_solcMappingSlot_any ⟨5⟩ owner mem) rfl (by evm_ov)
  have beforeDebit := runtime_run hashed with [swap5, swap1, swap5]
  obtain ⟨_, _, debited⟩ := beforeDebit.sstore writable (by decide +kernel) (by evm_ov)
  have beforeUnlock := runtime_run debited with [pop, pop, pop, push1 ⟨6⟩]
  obtain ⟨_, _, unlocked⟩ := beforeUnlock.sstore writable (by decide +kernel) (by evm_ov)
  exact ⟨_, _, _, _, runtime_run unlocked with [jump destination]⟩

end Rollup.EVM
