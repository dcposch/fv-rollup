import proofs.RuntimeBytecode

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Rollup.EVM

/-- A deposit rejects while the storage lock is set. -/
theorem deposit_bytecode_locked {I : ExecutionEnv} {g : Sat256} {s0 : Ethereum.State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : Nat}
    (stack : List UInt256) (space : stack.length + 2 ≤ 1024)
    (locked : (σ.find? I.codeOwner |>.option ⟨0⟩
      (fun account => account.storage.findD ⟨6⟩ ⟨0⟩)) ≠ ⟨0⟩)
    (reached : RD runtimeBytecode I g s0 ⟨1045⟩ stack mem aw rdata (cA, σ) k C) :
    RDrev runtimeBytecode g s0 := by
  have slot := runtime_run reached with [jumpdest, push1 ⟨6⟩]
  obtain ⟨_, _, loaded⟩ := slot.sload (by decide +kernel) (by evm_ov)
  have rejected := runtime_run loaded with [iszero, push2 ⟨1057⟩,
    jumpiNT (isZero_eq_zero_of_ne locked), push0, dup1]
  exact rejected.rev 0 (by decide +kernel)
    (fun s _ items => memExpRevert0 s items) (by evm_ov)

/-- An unlocked deposit sets the storage lock before it checks the owner. -/
theorem deposit_bytecode_enter {I : ExecutionEnv} {g : Sat256} {s0 : Ethereum.State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : Nat}
    (stack : List UInt256) (space : stack.length + 2 ≤ 1024)
    (writable : I.perm = true)
    (unlocked : (σ.find? I.codeOwner |>.option ⟨0⟩
      (fun account => account.storage.findD ⟨6⟩ ⟨0⟩)) = ⟨0⟩)
    (reached : RD runtimeBytecode I g s0 ⟨1045⟩ stack mem aw rdata (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g s0 ⟨1063⟩ stack mem aw rdata
      (cA, sstoreAccountMap I.codeOwner σ ⟨6⟩ ⟨1⟩) k' C' := by
  have slot := runtime_run reached with [jumpdest, push1 ⟨6⟩]
  obtain ⟨_, _, loaded⟩ := slot.sload (by decide +kernel) (by evm_ov)
  rw [unlocked] at loaded
  have acquired := runtime_run loaded with [iszero, push2 ⟨1057⟩,
    jumpiT (by decide) (jumpScan_valid runtimeBytecode 1057 1080 (by decide +kernel)),
    jumpdest, push1 ⟨1⟩, push1 ⟨6⟩]
  exact acquired.sstore writable (by decide +kernel) (by evm_ov)

/-- A valid owner passes both owner checks without account writes. -/
theorem deposit_bytecode_owner_ok {I : ExecutionEnv} {g : Sat256} {s0 : Ethereum.State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (owner : UInt256) (rest : List UInt256) (space : rest.length + 5 ≤ 1024)
    (canonical : owner.toNat < _root_.EVM.addressModulus)
    (nonzero : owner ≠ ⟨0⟩)
    (notSelf : UInt256.ofNat I.codeOwner.val ≠ owner)
    (reached : RD runtimeBytecode I g s0 ⟨1063⟩ (owner :: rest) mem aw rdata acc k C) :
    ∃ k' C', RD runtimeBytecode I g s0 ⟨1103⟩ (owner :: rest) mem aw rdata acc k' C' := by
  have mask : UInt256.sub (UInt256.shiftLeft ⟨1⟩ ⟨160⟩) ⟨1⟩ = solcAddrMask := by decide
  have first := runtime_run reached with [push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩,
    shl, sub, dup2, and, iszero, dup1, iszero, swap1, push2 ⟨1095⟩]
  rw [mask, solcAddrMask_clean canonical, isZero_eq_zero_of_ne nonzero] at first
  have second := runtime_run first with [jumpiNT rfl, pop, push1 ⟨1⟩, push1 ⟨1⟩,
    push1 ⟨160⟩, shl, sub, dup2, and, address, eq, iszero, jumpdest, push2 ⟨1103⟩]
  rw [mask, solcAddrMask_clean canonical, u256_eq_of_ne notSelf] at second
  exact ⟨_, _, runtime_run second with [
    jumpiT (by decide) (jumpScan_valid runtimeBytecode 1103 1120 (by decide +kernel))]⟩

/-- A deposit with ETH passes the call-value check. -/
theorem deposit_bytecode_value_ok {I : ExecutionEnv} {g : Sat256} {s0 : Ethereum.State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (stack : List UInt256) (space : stack.length + 2 ≤ 1024)
    (nonzero : I.weiValue ≠ ⟨0⟩)
    (reached : RD runtimeBytecode I g s0 ⟨1103⟩ stack mem aw rdata acc k C) :
    ∃ k' C', RD runtimeBytecode I g s0 ⟨1114⟩ stack mem aw rdata acc k' C' := by
  exact ⟨_, _, runtime_run reached with [jumpdest, callvalue, push0, sub, push2 ⟨1114⟩,
    jumpiT (u256_zero_sub_ne_zero nonzero)
      (jumpScan_valid runtimeBytecode 1114 1130 (by decide +kernel))]⟩

/-- A deposit with no ETH reverts. -/
theorem deposit_bytecode_zero_value {I : ExecutionEnv} {g : Sat256} {s0 : Ethereum.State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (stack : List UInt256) (space : stack.length + 2 ≤ 1024)
    (zero : I.weiValue = ⟨0⟩)
    (reached : RD runtimeBytecode I g s0 ⟨1103⟩ stack mem aw rdata acc k C) :
    RDrev runtimeBytecode g s0 := by
  have guard := runtime_run reached with [jumpdest, callvalue, push0, sub, push2 ⟨1114⟩]
  rw [zero] at guard
  have rejected := runtime_run guard with [jumpiNT (by decide), push0, dup1]
  exact rejected.rev 0 (by decide +kernel)
    (fun s _ items => memExpRevert0 s items) (by evm_ov)

end Rollup.EVM
