import proofs.RuntimeScalarGetter
import proofs.RuntimeMappingMemory
import proofs.RuntimeDecodeReject

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Rollup.EVM

inductive MappingGetter where
  | pendingDeposits | pendingWithdrawals

def mappingEntry : MappingGetter → UInt256
  | .pendingDeposits => ⟨336⟩
  | .pendingWithdrawals => ⟨398⟩

def mappingSlot : MappingGetter → UInt256
  | .pendingDeposits => ⟨4⟩
  | .pendingWithdrawals => ⟨5⟩

def mappingSelector : MappingGetter → UInt256
  | .pendingDeposits => ⟨0xeb3349b9⟩
  | .pendingWithdrawals => ⟨0xf3f43703⟩

private theorem mapping_guard_destination (getter : MappingGetter) :
    (D_J runtimeBytecode 0).contains (mappingEntry getter + ⟨11⟩) = true := by
  cases getter with
  | pendingDeposits => exact jumpScan_valid runtimeBytecode 347 440 (by decide +kernel)
  | pendingWithdrawals => exact jumpScan_valid runtimeBytecode 409 440 (by decide +kernel)

theorem mapping_body_destination (getter : MappingGetter) :
    (D_J runtimeBytecode 0).contains (mappingEntry getter + ⟨26⟩) = true := by
  cases getter with
  | pendingDeposits => exact jumpScan_valid runtimeBytecode 362 440 (by decide +kernel)
  | pendingWithdrawals => exact jumpScan_valid runtimeBytecode 424 440 (by decide +kernel)

/-- The credit getters reject call value. -/
theorem mapping_getter_nonpayable {I : ExecutionEnv} {g : Sat256} {s0 : Ethereum.State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (getter : MappingGetter) (rest : List UInt256) (space : rest.length + 3 ≤ 1024)
    (value : I.weiValue ≠ ⟨0⟩)
    (reached : RD runtimeBytecode I g s0 (mappingEntry getter) rest mem aw rdata acc k C) :
    RDrev runtimeBytecode g s0 := by
  have guarded := runtime_cases_run getter from reached with [jumpdest, callvalue, dup1, iszero,
    push2 (mappingEntry getter + ⟨11⟩)]
  have rejected := runtime_cases_run getter from guarded with [jumpiNT (isZero_eq_zero_of_ne value), push0, dup1]
  exact rejected.rev 0 (by cases getter <;> decide +kernel)
    (fun s _ stack => memExpRevert0 s stack) (by evm_ov)

/-- The credit getters enter the address decoder after the value check. -/
theorem mapping_getter_decoder {I : ExecutionEnv} {g : Sat256} {s0 : Ethereum.State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (getter : MappingGetter) (rest : List UInt256) (space : rest.length + 5 ≤ 1024)
    (value : I.weiValue = ⟨0⟩)
    (reached : RD runtimeBytecode I g s0 (mappingEntry getter) rest mem aw rdata acc k C) :
    ∃ k' C', RD runtimeBytecode I g s0 ⟨1331⟩
      (⟨4⟩ :: UInt256.ofNat I.calldata.size :: (mappingEntry getter + ⟨26⟩) :: ⟨249⟩ :: rest)
      mem aw rdata acc k' C' := by
  have guarded := runtime_cases_run getter from reached with [jumpdest, callvalue, dup1, iszero,
    push2 (mappingEntry getter + ⟨11⟩)]
  exact ⟨_, _, runtime_cases_run getter from guarded with [
    jumpiT (by rw [value]; decide) (mapping_guard_destination getter), jumpdest, pop,
    push2 ⟨249⟩, push2 (mappingEntry getter + ⟨26⟩), calldatasize, push1 ⟨4⟩, push2 ⟨1331⟩,
    jump (jumpScan_valid runtimeBytecode 1331 1360 (by decide +kernel))]⟩

/-- Each credit getter hashes its key and returns the stored credit. -/
theorem mapping_getter_return {I : ExecutionEnv} {g : Sat256} {s0 : Ethereum.State}
    {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : Nat}
    (getter : MappingGetter) (owner : UInt256) (rest : List UInt256)
    (space : rest.length + 5 ≤ 1024)
    (reached : RD runtimeBytecode I g s0 (mappingEntry getter + ⟨26⟩)
      (owner :: ⟨249⟩ :: rest) solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k C) :
    RDret runtimeBytecode g s0 (cA, σ)
      (UInt256.toByteArray (solcSlotWord σ I (solcMappingSlot (mappingSlot getter) owner))) := by
  have beforeSlot := runtime_cases_run getter from reached with [jumpdest,
    push1 (mappingSlot getter), push1 ⟨32⟩]
  have savedSlot := beforeSlot.mstore 0 (solcMappingBaseSlotMem (mappingSlot getter))
    (UInt256.ofNat 3) (by cases getter <;> decide +kernel) mem_cost rfl (by decide) (by evm_ov)
  have beforeOwner := runtime_cases_run getter from savedSlot with [push0, swap1, dup2]
  have savedOwner := beforeOwner.mstore 0 (solcMappingHashMem (mappingSlot getter) owner)
    (UInt256.ofNat 3) (by cases getter <;> decide +kernel) mem_cost rfl (by decide) (by evm_ov)
  have beforeHash := runtime_cases_run getter from savedOwner with [push1 ⟨64⟩, swap1]
  have hashed := beforeHash.keccak256 0 (solcMappingSlot (mappingSlot getter) owner) (UInt256.ofNat 3)
    (by cases getter <;> decide +kernel) mem_cost (solcMappingKeccakSlot _ _) (by decide) (by evm_ov)
  obtain ⟨_, _, loaded⟩ := hashed.sload (by cases getter <;> decide +kernel) (by evm_ov)
  have returning := runtime_cases_run getter from loaded with [dup2,
    jump (jumpScan_valid runtimeBytecode 249 270 (by decide +kernel))]
  exact runtime_return_word _ (⟨249⟩ :: rest) (by evm_ov)
    (solcMappingHashMem_mload64 _ _) rfl (mapping_return_pointer _ _ _)
    (mapping_return_read128 _ _ _) returning

end Rollup.EVM
