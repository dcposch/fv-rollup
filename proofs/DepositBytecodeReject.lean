import proofs.DepositBytecodeGuards

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Rollup.EVM

/-- A zero deposit owner reverts after the lock is set. -/
theorem deposit_bytecode_zero_owner {I : ExecutionEnv} {g : Sat256} {s0 : Ethereum.State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (rest : List UInt256) (space : rest.length + 5 ≤ 1024)
    (reached : RD runtimeBytecode I g s0 ⟨1063⟩ (⟨0⟩ :: rest) mem aw rdata acc k C) :
    RDrev runtimeBytecode g s0 := by
  have guard := runtime_run reached with [push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩,
    shl, sub, dup2, and, iszero, dup1, iszero, swap1, push2 ⟨1095⟩,
    jumpiT (by decide) (jumpScan_valid runtimeBytecode 1095 1110 (by decide +kernel)),
    jumpdest, push2 ⟨1103⟩, jumpiNT (by decide), push0, dup1]
  exact guard.rev 0 (by decide +kernel)
    (fun s _ items => memExpRevert0 s items) (by evm_ov)

/-- The rollup cannot be the owner of deposit credit. -/
theorem deposit_bytecode_self_owner {I : ExecutionEnv} {g : Sat256} {s0 : Ethereum.State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (owner : UInt256) (rest : List UInt256) (space : rest.length + 5 ≤ 1024)
    (canonical : owner.toNat < _root_.EVM.addressModulus)
    (nonzero : owner ≠ ⟨0⟩) (self : UInt256.ofNat I.codeOwner.val = owner)
    (reached : RD runtimeBytecode I g s0 ⟨1063⟩ (owner :: rest) mem aw rdata acc k C) :
    RDrev runtimeBytecode g s0 := by
  have mask : UInt256.sub (UInt256.shiftLeft ⟨1⟩ ⟨160⟩) ⟨1⟩ = solcAddrMask := by decide
  have first := runtime_run reached with [push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩,
    shl, sub, dup2, and, iszero, dup1, iszero, swap1, push2 ⟨1095⟩]
  rw [mask, solcAddrMask_clean canonical, isZero_eq_zero_of_ne nonzero] at first
  have second := runtime_run first with [jumpiNT rfl, pop, push1 ⟨1⟩, push1 ⟨1⟩,
    push1 ⟨160⟩, shl, sub, dup2, and, address, eq, iszero, jumpdest, push2 ⟨1103⟩]
  rw [mask, solcAddrMask_clean canonical, self, u256_eq_refl] at second
  have rejected := runtime_run second with [jumpiNT (by decide), push0, dup1]
  exact rejected.rev 0 (by decide +kernel)
    (fun s _ items => memExpRevert0 s items) (by evm_ov)

end Rollup.EVM
