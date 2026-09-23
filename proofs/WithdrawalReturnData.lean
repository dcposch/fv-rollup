import proofs.WithdrawalPaymentSetup

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Rollup.EVM

/-- Return-data handling preserves the status and saved credit for every returned byte string. -/
theorem withdrawal_bytecode_return_data {I : ExecutionEnv} {g : Sat256} {s0 : Ethereum.State}
    {mem : ByteArray} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (status credit amount owner : UInt256) (rest : List UInt256) (space : rest.length + 16 ≤ 1024)
    (memorySize : mem.size = 96)
    (freePointer : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (reached : RD runtimeBytecode I g s0 ⟨936⟩
      (status :: ⟨128⟩ :: amount :: owner :: ⟨0⟩ :: credit :: amount :: owner :: rest)
      mem (UInt256.ofNat 3) rdata acc k C) :
    ∃ mem' aw' k' C', RD runtimeBytecode I g s0 ⟨991⟩
      (status :: credit :: amount :: owner :: rest) mem' aw' rdata acc k' C' := by
  have guard := runtime_run reached with [swap3, pop, pop, pop,
    returndatasize, dup1, push0, dup2, eq, push2 ⟨981⟩]
  by_cases zero : UInt256.ofNat rdata.size = ⟨0⟩
  · have empty := runtime_run guard with [jumpiT (by rw [zero]; decide)
      (jumpScan_valid runtimeBytecode 981 1000 (by decide +kernel)),
      jumpdest, push1 ⟨96⟩, swap2, pop, jumpdest, pop, pop, swap1, pop]
    exact ⟨_, _, _, _, empty⟩
  · have dataEntry := runtime_run guard with [jumpiNT (u256_eq_of_ne zero), push1 ⟨64⟩]
    have pointer := dataEntry.mload 0 ⟨128⟩ (UInt256.ofNat 3)
      (by decide +kernel) mem_cost
      (mloadFreePtrValue (by rw [memorySize]; decide) (by decide) freePointer)
      (by decide) (by evm_ov)
    have beforeAlloc := runtime_run pointer with [swap2, pop, push1 ⟨31⟩, not,
      push1 ⟨63⟩, returndatasize, add, and, dup3, add, push1 ⟨64⟩]
    have allocated := beforeAlloc.mstore 0 _ (UInt256.ofNat 3)
      (by decide +kernel) mem_cost rfl (by decide) (by evm_ov)
    have beforeLength := runtime_run allocated with [returndatasize, dup3]
    have lengthStored := beforeLength.mstore 6 _ (UInt256.ofNat 5)
      (by decide +kernel) mem_cost rfl (by decide) (by evm_ov)
    have beforeCopy := runtime_run lengthStored with [returndatasize, push0, push1 ⟨32⟩, dup5, add]
    have copied := beforeCopy.returndatacopy
      (Cₘ (UInt256.ofNat (MachineState.M 5 160 (UInt256.ofNat rdata.size).toNat)) - Cₘ (UInt256.ofNat 5))
      _ (UInt256.ofNat (MachineState.M 5 160 (UInt256.ofNat rdata.size).toNat))
      (by decide +kernel)
      (by
        change 0 + (UInt256.ofNat rdata.size).toNat ≤ rdata.size
        simpa only [Nat.zero_add] using Nat.mod_le rdata.size UInt256.size)
      (by
        intro state words stack
        simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', words, stack,
          List.getElem!_cons_zero, List.getElem!_cons_succ]
        rfl)
      rfl rfl (by evm_ov)
    have finished := runtime_run copied with [push2 ⟨986⟩,
      jump (jumpScan_valid runtimeBytecode 986 1000 (by decide +kernel)),
      jumpdest, pop, pop, swap1, pop]
    exact ⟨_, _, _, _, finished⟩

end Rollup.EVM
