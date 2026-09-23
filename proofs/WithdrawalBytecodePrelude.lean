import proofs.support.WithdrawalChecks
import proofs.WithdrawalEntry

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Rollup.EVM

/-- The withdrawal amount must be nonzero before credit is read. -/
theorem withdrawal_bytecode_amount {I : ExecutionEnv} {g : Sat256} {s0 : Ethereum.State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (amount owner : UInt256) (rest : List UInt256) (space : rest.length + 5 ≤ 1024)
    (reached : RD runtimeBytecode I g s0 ⟨861⟩ (amount :: owner :: rest) mem aw rdata acc k C) :
    (RDrev runtimeBytecode g s0 ∧ amount = ⟨0⟩) ∨
      (amount ≠ ⟨0⟩ ∧ ∃ k' C', RD runtimeBytecode I g s0 ⟨872⟩
        (amount :: owner :: rest) mem aw rdata acc k' C') := by
  have guard := runtime_run reached with [push0, dup2, swap1, sub, push2 ⟨872⟩]
  by_cases zero : amount = ⟨0⟩
  · rw [zero] at guard
    have rejected := runtime_run guard with [jumpiNT (by decide), push0, dup1]
    exact .inl ⟨rejected.rev 0 (by decide +kernel)
      (fun s _ items => memExpRevert0 s items) (by evm_ov), zero⟩
  · exact .inr ⟨zero, _, _, runtime_run guard with [jumpiT (u256_zero_sub_ne_zero zero)
      (jumpScan_valid runtimeBytecode 872 900 (by decide +kernel))]⟩

/-- Load withdrawal credit from the decoded owner's mapping slot. -/
theorem withdrawal_bytecode_credit_load {I : ExecutionEnv} {g : Sat256} {s0 : Ethereum.State}
    {mem : ByteArray} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : Nat}
    (rest : List UInt256) (space : rest.length + 7 ≤ 1024)
    (canonical : (calldataWord I.calldata 4).toNat < _root_.EVM.addressModulus)
    (memorySize : mem.size = 96)
    (reached : RD runtimeBytecode I g s0 ⟨872⟩
      (calldataWord I.calldata 36 :: calldataWord I.calldata 4 :: rest)
      mem (UInt256.ofNat 3) rdata (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g s0 ⟨897⟩
      (withdrawalClaimWord σ I :: calldataWord I.calldata 36 :: calldataWord I.calldata 4 :: rest)
      (twoWordHashMem (calldataWord I.calldata 4) ⟨5⟩ mem) (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
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

/-- Payment setup starts only when credit covers the amount. -/
theorem withdrawal_bytecode_credit_check {I : ExecutionEnv} {g : Sat256} {s0 : Ethereum.State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (credit amount owner : UInt256) (rest : List UInt256) (space : rest.length + 6 ≤ 1024)
    (reached : RD runtimeBytecode I g s0 ⟨897⟩ (credit :: amount :: owner :: rest)
      mem aw rdata acc k C) :
    (RDrev runtimeBytecode g s0 ∧ ¬ amount.toNat ≤ credit.toNat) ∨
      (amount.toNat ≤ credit.toNat ∧ ∃ k' C', RD runtimeBytecode I g s0 ⟨908⟩
        (credit :: amount :: owner :: rest) mem aw rdata acc k' C') := by
  have guard := runtime_run reached with [dup1, dup3, gt, iszero, push2 ⟨908⟩]
  by_cases covered : amount.toNat ≤ credit.toNat
  · exact .inr ⟨covered, _, _, runtime_run guard with [jumpiT (by rw [ugt_zero covered]; decide)
      (jumpScan_valid runtimeBytecode 908 940 (by decide +kernel))]⟩
  · have tooLarge : UInt256.gt amount credit = ⟨1⟩ := ugt_one (by omega)
    have rejected := runtime_run guard with [jumpiNT (by rw [tooLarge]; decide), push0, dup1]
    exact .inl ⟨rejected.rev 0 (by decide +kernel)
      (fun s _ items => memExpRevert0 s items) (by evm_ov), covered⟩

end Rollup.EVM
