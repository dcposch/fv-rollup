import semantics.Bytecode
import Reasoning.Solc
import Reasoning.Initcode
import proofs.BytecodeSteps

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Rollup.EVM

theorem creation_prefix_size : creationPrefix.size = 165 := by decide

theorem runtime_size : runtimeBytecode.size = 1429 := by decide

theorem creation_size : creationBytecode.size = 1594 := by
  rw [creationBytecode, ByteArray.size_append, creation_prefix_size, runtime_size]

theorem creation_runtime_window : creationBytecode.extract 165 1594 = runtimeBytecode := by
  exact extract_append_right' creationPrefix runtimeBytecode 165 1594
    creation_prefix_size.symm (by rw [creation_prefix_size, runtime_size])

/-- Constructor arguments cannot change decoding in the creation prefix. -/
theorem creation_decode (args : ByteArray) (pc : UInt256) (hpc : pc.toNat < 165) :
    decode (creationBytecode ++ args) pc = decode creationBytecode pc := by
  apply decode_append_left_window
  · rw [creation_size]
    omega
  · rw [creation_size]; decide

/-- A constructor call with ETH reverts or runs out of gas. -/
theorem creation_nonpayable {cA gh bl σ σ₀ A I} {g : Sat256} (args : ByteArray)
    (hcode : I.code = creationBytecode ++ args) (value : I.weiValue ≠ ⟨0⟩) :
    RDrev (creationBytecode ++ args) g (initState cA gh bl σ σ₀ g A I) := by
  have dec := creation_decode args
  have start := solcGuardPrologueRD (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (g := g) hcode
    (by rw [dec _ (by decide)]; decide)
    (by rw [dec _ (by decide)]; decide)
    (by rw [dec _ (by decide)]; decide)
    (by rw [dec _ (by decide)]; decide)
    (by rw [dec _ (by decide)]; decide)
    (by rw [dec _ (by decide)]; decide)
  exact start.push1 ⟨14⟩ (by rw [dec _ (by decide)]; decide) (by evm_ov)
    |>.jumpiNT (by rw [dec _ (by decide)]; decide) (isZero_eq_zero_of_ne value) (by evm_ov)
    |>.push0 (by rw [dec _ (by decide)]; decide) (by evm_ov)
    |>.dup1 (by rw [dec _ (by decide)]; decide) (by evm_ov)
    |>.rev 0 (by rw [dec _ (by decide)]; decide)
      (fun s _ stack => memExpRevert0 s stack) (by evm_ov)

/-- The zero-value guard reaches the constructor body without account changes. -/
theorem creation_zero_value {cA gh bl σ σ₀ A I} {g : Sat256} (args : ByteArray)
    (hcode : I.code = creationBytecode ++ args) (value : I.weiValue = ⟨0⟩) :
    ∃ k C, RD (creationBytecode ++ args) I g (initState cA gh bl σ σ₀ g A I)
      ⟨16⟩ [] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have dec := creation_decode args
  exact solcGuardCallvalueZero (ctgt := ⟨14⟩) (opC := .PUSH1) (wC := 1)
    (solcGuardPrologueRD hcode
      (by rw [dec _ (by decide)]; decide)
      (by rw [dec _ (by decide)]; decide)
      (by rw [dec _ (by decide)]; decide)
      (by rw [dec _ (by decide)]; decide)
      (by rw [dec _ (by decide)]; decide)
      (by rw [dec _ (by decide)]; decide))
    value (by decide)
    (by rw [dec _ (by decide)]; decide)
    (by rw [dec _ (by decide)]; decide)
    (by rw [dec _ (by decide)]; decide)
    (by rw [dec _ (by decide)]; decide)
    (D_J_contains_append_left _ args _ (jumpScan_valid creationBytecode 14 20 (by decide)))

/-- The return block copies the pinned runtime bytes, independent of arguments. -/
theorem creation_return_bytes (args mem : ByteArray) :
    ((creationBytecode ++ args).write 165 mem 0 1429).readWithPadding 0 1429 =
      runtimeBytecode := by
  rw [write0_read_back_from_gen _ _ _ _ (by decide)
    (by rw [ByteArray.size_append, creation_size]; omega) (by decide)]
  rw [byteArray_extract_append_left _ _ _ _ (by rw [creation_size])]
  exact creation_runtime_window

/-- Once reached, the constructor return block preserves accounts and returns runtime code. -/
theorem creation_return {I : ExecutionEnv} {g : Sat256} {s0 : Ethereum.State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (args mem : ByteArray)
    (reached : RD (creationBytecode ++ args) I g s0 ⟨152⟩ [] mem
      (UInt256.ofNat 6) ByteArray.empty acc k C) :
    RDret (creationBytecode ++ args) g s0 acc runtimeBytecode := by
  have dec := creation_decode args
  have copy := reached.jumpdest (by rw [dec _ (by decide)]; decide) (by evm_ov)
    |>.push2 ⟨1429⟩ (by rw [dec _ (by decide)]; decide) (by evm_ov)
    |>.dup1 (by rw [dec _ (by decide)]; decide) (by evm_ov)
    |>.push2 ⟨165⟩ (by rw [dec _ (by decide)]; decide) (by evm_ov)
    |>.push0 (by rw [dec _ (by decide)]; decide) (by evm_ov)
  have copied := copy.codecopy 120 ((creationBytecode ++ args).write 165 mem 0 1429)
    (UInt256.ofNat 45) (by rw [dec _ (by decide)]; decide)
    mem_cost rfl (by decide) (by evm_ov)
  exact copied.push0 (by rw [dec _ (by decide)]; decide) (by evm_ov)
    |>.ret 0 runtimeBytecode (by rw [dec _ (by decide)]; decide)
      mem_cost (creation_return_bytes args mem) (by evm_ov)

end Rollup.EVM
