import proofs.RuntimeBytecode

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Rollup.EVM

/-- Checked addition reverts when the sum does not fit in one word. -/
theorem runtime_checked_add_overflow {I : ExecutionEnv} {g : Sat256} {s0 : Ethereum.State}
    {mem : ByteArray} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (a b ret : UInt256) (rest : List UInt256) (space : rest.length + 8 ≤ 1024)
    (overflow : UInt256.size ≤ a.toNat + b.toNat)
    (reached : RD runtimeBytecode I g s0 ⟨1385⟩ (b :: a :: ret :: rest)
      mem (UInt256.ofNat 3) rdata acc k C) :
    RDrev runtimeBytecode g s0 := by
  have aBound : a.toNat < UInt256.size := a.val.isLt
  have bBound : b.toNat < UInt256.size := b.val.isLt
  have sumNat : (a + b).toNat = a.toNat + b.toNat - UInt256.size := by
    rw [uadd_toNat, Nat.mod_eq_sub_mod overflow, Nat.mod_eq_of_lt (by omega)]
  have compare : UInt256.gt b (a + b) = ⟨1⟩ := ugt_one (by rw [sumNat]; omega)
  have checked := runtime_run reached with [jumpdest, dup1, dup3, add, dup1, dup3,
    gt, iszero, push2 ⟨1404⟩]
  rw [compare] at checked
  have beforeSelector := runtime_run checked with [jumpiNT (by decide),
    push2 ⟨1404⟩, push2 ⟨1365⟩,
    jump (jumpScan_valid runtimeBytecode 1365 1380 (by decide +kernel)),
    jumpdest, push4 ⟨0x4e487b71⟩, push1 ⟨224⟩, shl, push0]
  have selectorStored := beforeSelector.mstore 0 _ (UInt256.ofNat 3)
    (by decide +kernel) mem_cost rfl (by decide) (by evm_ov)
  have beforeCode := runtime_run selectorStored with [push1 ⟨17⟩, push1 ⟨4⟩]
  have codeStored := beforeCode.mstore 0 _ (UInt256.ofNat 3)
    (by decide +kernel) mem_cost rfl (by decide) (by evm_ov)
  have rejected := runtime_run codeStored with [push1 ⟨36⟩, push0]
  exact rejected.rev 0 (by decide +kernel)
    (fun s active items => by rw [memExpRevertZeroOff s items, active]; decide)
    (by evm_ov)

end Rollup.EVM
