import proofs.RuntimeBytecode

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Rollup.EVM

/-- A batch rejects while the storage lock is set. -/
theorem batch_bytecode_locked {I : ExecutionEnv} {g : Sat256} {s0 : Ethereum.State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : Nat}
    (stack : List UInt256) (space : stack.length + 2 ≤ 1024)
    (locked : (σ.find? I.codeOwner |>.option ⟨0⟩
      (fun account => account.storage.findD ⟨6⟩ ⟨0⟩)) ≠ ⟨0⟩)
    (reached : RD runtimeBytecode I g s0 ⟨441⟩ stack mem aw rdata (cA, σ) k C) :
    RDrev runtimeBytecode g s0 := by
  have slot := runtime_run reached with [jumpdest, push1 ⟨6⟩]
  obtain ⟨_, _, loaded⟩ := slot.sload (by decide +kernel) (by evm_ov)
  have rejected := runtime_run loaded with [iszero, push2 ⟨453⟩,
    jumpiNT (isZero_eq_zero_of_ne locked), push0, dup1]
  exact rejected.rev 0 (by decide +kernel)
    (fun s _ items => memExpRevert0 s items) (by evm_ov)

/-- An unlocked batch sets the storage lock before it changes credit. -/
theorem batch_bytecode_enter {I : ExecutionEnv} {g : Sat256} {s0 : Ethereum.State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : Nat}
    (stack : List UInt256) (space : stack.length + 2 ≤ 1024)
    (writable : I.perm = true)
    (unlocked : (σ.find? I.codeOwner |>.option ⟨0⟩
      (fun account => account.storage.findD ⟨6⟩ ⟨0⟩)) = ⟨0⟩)
    (reached : RD runtimeBytecode I g s0 ⟨441⟩ stack mem aw rdata (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g s0 ⟨459⟩ stack mem aw rdata
      (cA, sstoreAccountMap I.codeOwner σ ⟨6⟩ ⟨1⟩) k' C' := by
  have slot := runtime_run reached with [jumpdest, push1 ⟨6⟩]
  obtain ⟨_, _, loaded⟩ := slot.sload (by decide +kernel) (by evm_ov)
  rw [unlocked] at loaded
  have acquired := runtime_run loaded with [iszero, push2 ⟨453⟩,
    jumpiT (by decide) (jumpScan_valid runtimeBytecode 453 480 (by decide +kernel)),
    jumpdest, push1 ⟨1⟩, push1 ⟨6⟩]
  exact acquired.sstore writable (by decide +kernel) (by evm_ov)


/-- A withdrawal rejects while the storage lock is set. -/
theorem withdrawal_bytecode_locked {I : ExecutionEnv} {g : Sat256} {s0 : Ethereum.State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : Nat}
    (stack : List UInt256) (space : stack.length + 2 ≤ 1024)
    (locked : (σ.find? I.codeOwner |>.option ⟨0⟩
      (fun account => account.storage.findD ⟨6⟩ ⟨0⟩)) ≠ ⟨0⟩)
    (reached : RD runtimeBytecode I g s0 ⟨843⟩ stack mem aw rdata (cA, σ) k C) :
    RDrev runtimeBytecode g s0 := by
  have slot := runtime_run reached with [jumpdest, push1 ⟨6⟩]
  obtain ⟨_, _, loaded⟩ := slot.sload (by decide +kernel) (by evm_ov)
  have rejected := runtime_run loaded with [iszero, push2 ⟨855⟩,
    jumpiNT (isZero_eq_zero_of_ne locked), push0, dup1]
  exact rejected.rev 0 (by decide +kernel)
    (fun s _ items => memExpRevert0 s items) (by evm_ov)

/-- An unlocked withdrawal sets the storage lock before it changes credit. -/
theorem withdrawal_bytecode_enter {I : ExecutionEnv} {g : Sat256} {s0 : Ethereum.State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : Nat}
    (stack : List UInt256) (space : stack.length + 2 ≤ 1024)
    (writable : I.perm = true)
    (unlocked : (σ.find? I.codeOwner |>.option ⟨0⟩
      (fun account => account.storage.findD ⟨6⟩ ⟨0⟩)) = ⟨0⟩)
    (reached : RD runtimeBytecode I g s0 ⟨843⟩ stack mem aw rdata (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g s0 ⟨861⟩ stack mem aw rdata
      (cA, sstoreAccountMap I.codeOwner σ ⟨6⟩ ⟨1⟩) k' C' := by
  have slot := runtime_run reached with [jumpdest, push1 ⟨6⟩]
  obtain ⟨_, _, loaded⟩ := slot.sload (by decide +kernel) (by evm_ov)
  rw [unlocked] at loaded
  have acquired := runtime_run loaded with [iszero, push2 ⟨855⟩,
    jumpiT (by decide) (jumpScan_valid runtimeBytecode 855 880 (by decide +kernel)),
    jumpdest, push1 ⟨1⟩, push1 ⟨6⟩]
  exact acquired.sstore writable (by decide +kernel) (by evm_ov)

end Rollup.EVM
