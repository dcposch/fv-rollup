import proofs.WithdrawalPrefixEntry
import proofs.PrefixStorage
import proofs.PrefixPermission
import proofs.WithdrawalBytecodeChecks

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Rollup.EVM

/-- Load withdrawal credit from the decoded owner's mapping slot. -/
theorem withdrawal_prefix_credit_load {I : ExecutionEnv} {target child : Ethereum.State}
    {mem : ByteArray} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (rest : List UInt256) (space : rest.length + 7 ≤ 1024)
    (canonical : (calldataWord I.calldata 4).toNat < _root_.EVM.addressModulus)
    (memorySize : mem.size = 96)
    (reached : PCR runtimeBytecode I target child ⟨872⟩
      (calldataWord I.calldata 36 :: calldataWord I.calldata 4 :: rest)
      mem (UInt256.ofNat 3) rdata (cA, σ)) :
    PCR runtimeBytecode I target child ⟨897⟩
      (withdrawalClaimWord σ I :: calldataWord I.calldata 36 :: calldataWord I.calldata 4 :: rest)
      (twoWordHashMem (calldataWord I.calldata 4) ⟨5⟩ mem) (UInt256.ofNat 3) rdata (cA, σ) := by
  have mask : UInt256.sub (UInt256.shiftLeft ⟨1⟩ ⟨160⟩) ⟨1⟩ = solcAddrMask := by decide
  have cleaned := runtime_run reached with [jumpdest, push1 ⟨1⟩, push1 ⟨1⟩,
    push1 ⟨160⟩, shl, sub, dup3, and]
  rw [mask, solcAddrMask_clean canonical] at cleaned
  have beforeOwner := runtime_run cleaned with [push0, swap1, dup2]
  have ownerStored := beforeOwner.mstore 0 (wordAt0Mem (calldataWord I.calldata 4) mem) (UInt256.ofNat 3)
    (by decide +kernel) mem_cost rfl (by decide) (by evm_ov)
  have beforeSlot := runtime_run ownerStored with [push1 ⟨5⟩, push1 ⟨32⟩]
  have slotStored := beforeSlot.mstore 0 (twoWordHashMem (calldataWord I.calldata 4) ⟨5⟩ mem)
    (UInt256.ofNat 3) (by decide +kernel) mem_cost rfl (by decide) (by evm_ov)
  have beforeHash := runtime_run slotStored with [push1 ⟨64⟩, swap1]
  have hashed := beforeHash.keccak256 0 (withdrawalClaimSlot I) (UInt256.ofNat 3)
    (by decide +kernel) mem_cost (twoWordHashMem_solcMappingSlot ⟨5⟩ _ memorySize)
    (by decide) (by evm_ov)
  exact hashed.sload (by decide +kernel) (by evm_ov)

end Rollup.EVM
