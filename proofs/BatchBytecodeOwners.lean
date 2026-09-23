import proofs.BatchEntry

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Rollup.EVM

/-- Check the deposit owner before the batch changes credit. -/
theorem batch_bytecode_deposit_owner_cases {I : ExecutionEnv} {g : Sat256} {s0 : Ethereum.State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (rest : List UInt256) (space : rest.length + 11 ≤ 1024)
    (canonical : (calldataWord I.calldata 100).toNat < _root_.EVM.addressModulus)
    (reached : RD runtimeBytecode I g s0 ⟨516⟩ (batchDecodedStack I rest) mem aw rdata acc k C) :
    (RDrev runtimeBytecode g s0 ∧ ¬(if calldataWord I.calldata 132 = ⟨0⟩ then calldataWord I.calldata 100 = ⟨0⟩
        else calldataWord I.calldata 100 ≠ ⟨0⟩ ∧
          UInt256.ofNat I.codeOwner.val ≠ calldataWord I.calldata 100)) ∨
      ((if calldataWord I.calldata 132 = ⟨0⟩ then calldataWord I.calldata 100 = ⟨0⟩
        else calldataWord I.calldata 100 ≠ ⟨0⟩ ∧
          UInt256.ofNat I.codeOwner.val ≠ calldataWord I.calldata 100) ∧
       ∃ k' C', RD runtimeBytecode I g s0 ⟨588⟩ (batchDecodedStack I rest) mem aw rdata acc k' C') := by
  dsimp only [batchDecodedStack] at reached
  have mask : UInt256.sub (UInt256.shiftLeft ⟨1⟩ ⟨160⟩) ⟨1⟩ = solcAddrMask := by decide
  have amountGuard := runtime_run reached with [jumpdest, dup3, push0, sub, push2 ⟨547⟩]
  by_cases empty : calldataWord I.calldata 132 = ⟨0⟩
  · have ownerGuard := runtime_run amountGuard with [jumpiNT (by rw [empty]; decide),
      push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup5, and, iszero, push2 ⟨542⟩]
    rw [mask, solcAddrMask_clean canonical] at ownerGuard
    by_cases zeroOwner : calldataWord I.calldata 100 = ⟨0⟩
    · have accepted := runtime_run ownerGuard with [jumpiT (by rw [zeroOwner]; decide)
        (jumpScan_valid runtimeBytecode 542 572 (by decide +kernel)),
        jumpdest, push2 ⟨588⟩,
        jump (jumpScan_valid runtimeBytecode 588 634 (by decide +kernel))]
      exact Or.inr ⟨by simp only [if_pos empty]; exact zeroOwner, _, _, accepted⟩
    · have rejected := runtime_run ownerGuard with [jumpiNT (isZero_eq_zero_of_ne zeroOwner), push0, dup1]
      exact Or.inl ⟨(rejected.rev 0 (by decide +kernel)
        (fun s _ items => memExpRevert0 s items) (by evm_ov)), by simpa only [if_pos empty] using zeroOwner⟩
  · have ownerGuard := runtime_run amountGuard with [jumpiT (u256_zero_sub_ne_zero empty)
      (jumpScan_valid runtimeBytecode 547 577 (by decide +kernel)),
      jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup5, and,
      iszero, dup1, iszero, swap1, push2 ⟨580⟩]
    rw [mask, solcAddrMask_clean canonical] at ownerGuard
    by_cases zeroOwner : calldataWord I.calldata 100 = ⟨0⟩
    · have rejected := runtime_run ownerGuard with [jumpiT (by rw [zeroOwner]; decide)
        (jumpScan_valid runtimeBytecode 580 610 (by decide +kernel)),
        jumpdest, push2 ⟨588⟩, jumpiNT (by rw [zeroOwner]; decide), push0, dup1]
      exact Or.inl ⟨(rejected.rev 0 (by decide +kernel)
        (fun s _ items => memExpRevert0 s items) (by evm_ov)), by simp only [if_neg empty, zeroOwner, ne_eq, not_true_eq_false, false_and, not_false_eq_true]⟩
    · have selfGuard := runtime_run ownerGuard with [jumpiNT (isZero_eq_zero_of_ne zeroOwner), pop,
        push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup5, and,
        address, eq, iszero, jumpdest, push2 ⟨588⟩]
      rw [mask, solcAddrMask_clean canonical] at selfGuard
      by_cases different : UInt256.ofNat I.codeOwner.val ≠ calldataWord I.calldata 100
      · have accepted := runtime_run selfGuard with [jumpiT (by rw [u256_eq_of_ne different]; decide)
          (jumpScan_valid runtimeBytecode 588 634 (by decide +kernel))]
        exact Or.inr ⟨by simp only [if_neg empty]; exact ⟨zeroOwner, different⟩, _, _, accepted⟩
      · have same := not_ne_iff.mp different
        have rejected := runtime_run selfGuard with [jumpiNT (by rw [same, u256_eq_refl]; rfl), push0, dup1]
        exact Or.inl ⟨(rejected.rev 0 (by decide +kernel)
          (fun s _ items => memExpRevert0 s items) (by evm_ov)), by simp only [if_neg empty]; intro checks; exact different checks.2⟩

/-- Discard the reason for rejection. -/
theorem batch_bytecode_deposit_owner {I : ExecutionEnv} {g : Sat256} {s0 : Ethereum.State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (rest : List UInt256) (space : rest.length + 11 ≤ 1024)
    (canonical : (calldataWord I.calldata 100).toNat < _root_.EVM.addressModulus)
    (reached : RD runtimeBytecode I g s0 ⟨516⟩ (batchDecodedStack I rest) mem aw rdata acc k C) :
    RDrev runtimeBytecode g s0 ∨
      ((if calldataWord I.calldata 132 = ⟨0⟩ then calldataWord I.calldata 100 = ⟨0⟩
        else calldataWord I.calldata 100 ≠ ⟨0⟩ ∧
          UInt256.ofNat I.codeOwner.val ≠ calldataWord I.calldata 100) ∧
       ∃ k' C', RD runtimeBytecode I g s0 ⟨588⟩ (batchDecodedStack I rest) mem aw rdata acc k' C') := by
  rcases batch_bytecode_deposit_owner_cases rest space canonical reached with ⟨rejected, _⟩ | accepted
  · exact Or.inl rejected
  · exact Or.inr accepted

/-- Check the withdrawal owner before the batch changes credit. -/
theorem batch_bytecode_withdrawal_owner_cases {I : ExecutionEnv} {g : Sat256} {s0 : Ethereum.State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (rest : List UInt256) (space : rest.length + 11 ≤ 1024)
    (canonical : (calldataWord I.calldata 164).toNat < _root_.EVM.addressModulus)
    (reached : RD runtimeBytecode I g s0 ⟨588⟩ (batchDecodedStack I rest) mem aw rdata acc k C) :
    (RDrev runtimeBytecode g s0 ∧ ¬(if calldataWord I.calldata 196 = ⟨0⟩ then calldataWord I.calldata 164 = ⟨0⟩
        else calldataWord I.calldata 164 ≠ ⟨0⟩ ∧
          UInt256.ofNat I.codeOwner.val ≠ calldataWord I.calldata 164)) ∨
      ((if calldataWord I.calldata 196 = ⟨0⟩ then calldataWord I.calldata 164 = ⟨0⟩
        else calldataWord I.calldata 164 ≠ ⟨0⟩ ∧
          UInt256.ofNat I.codeOwner.val ≠ calldataWord I.calldata 164) ∧
       ∃ k' C', RD runtimeBytecode I g s0 ⟨660⟩ (batchDecodedStack I rest) mem aw rdata acc k' C') := by
  dsimp only [batchDecodedStack] at reached
  have mask : UInt256.sub (UInt256.shiftLeft ⟨1⟩ ⟨160⟩) ⟨1⟩ = solcAddrMask := by decide
  have amountGuard := runtime_run reached with [jumpdest, dup1, push0, sub, push2 ⟨619⟩]
  by_cases empty : calldataWord I.calldata 196 = ⟨0⟩
  · have ownerGuard := runtime_run amountGuard with [jumpiNT (by rw [empty]; decide),
      push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup3, and, iszero, push2 ⟨614⟩]
    rw [mask, solcAddrMask_clean canonical] at ownerGuard
    by_cases zeroOwner : calldataWord I.calldata 164 = ⟨0⟩
    · have accepted := runtime_run ownerGuard with [jumpiT (by rw [zeroOwner]; decide)
        (jumpScan_valid runtimeBytecode 614 644 (by decide +kernel)),
        jumpdest, push2 ⟨660⟩,
        jump (jumpScan_valid runtimeBytecode 660 690 (by decide +kernel))]
      exact Or.inr ⟨by simp only [if_pos empty]; exact zeroOwner, _, _, accepted⟩
    · have rejected := runtime_run ownerGuard with [jumpiNT (isZero_eq_zero_of_ne zeroOwner), push0, dup1]
      exact Or.inl ⟨(rejected.rev 0 (by decide +kernel)
        (fun s _ items => memExpRevert0 s items) (by evm_ov)), by simpa only [if_pos empty] using zeroOwner⟩
  · have ownerGuard := runtime_run amountGuard with [jumpiT (u256_zero_sub_ne_zero empty)
      (jumpScan_valid runtimeBytecode 619 649 (by decide +kernel)),
      jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup3, and,
      iszero, dup1, iszero, swap1, push2 ⟨652⟩]
    rw [mask, solcAddrMask_clean canonical] at ownerGuard
    by_cases zeroOwner : calldataWord I.calldata 164 = ⟨0⟩
    · have rejected := runtime_run ownerGuard with [jumpiT (by rw [zeroOwner]; decide)
        (jumpScan_valid runtimeBytecode 652 682 (by decide +kernel)),
        jumpdest, push2 ⟨660⟩, jumpiNT (by rw [zeroOwner]; decide), push0, dup1]
      exact Or.inl ⟨(rejected.rev 0 (by decide +kernel)
        (fun s _ items => memExpRevert0 s items) (by evm_ov)), by simp only [if_neg empty, zeroOwner, ne_eq, not_true_eq_false, false_and, not_false_eq_true]⟩
    · have selfGuard := runtime_run ownerGuard with [jumpiNT (isZero_eq_zero_of_ne zeroOwner), pop,
        push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup3, and,
        address, eq, iszero, jumpdest, push2 ⟨660⟩]
      rw [mask, solcAddrMask_clean canonical] at selfGuard
      by_cases different : UInt256.ofNat I.codeOwner.val ≠ calldataWord I.calldata 164
      · have accepted := runtime_run selfGuard with [jumpiT (by rw [u256_eq_of_ne different]; decide)
          (jumpScan_valid runtimeBytecode 660 690 (by decide +kernel))]
        exact Or.inr ⟨by simp only [if_neg empty]; exact ⟨zeroOwner, different⟩, _, _, accepted⟩
      · have same := not_ne_iff.mp different
        have rejected := runtime_run selfGuard with [jumpiNT (by rw [same, u256_eq_refl]; rfl), push0, dup1]
        exact Or.inl ⟨(rejected.rev 0 (by decide +kernel)
          (fun s _ items => memExpRevert0 s items) (by evm_ov)), by simp only [if_neg empty]; intro checks; exact different checks.2⟩

/-- Discard the reason for rejection. -/
theorem batch_bytecode_withdrawal_owner {I : ExecutionEnv} {g : Sat256} {s0 : Ethereum.State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (rest : List UInt256) (space : rest.length + 11 ≤ 1024)
    (canonical : (calldataWord I.calldata 164).toNat < _root_.EVM.addressModulus)
    (reached : RD runtimeBytecode I g s0 ⟨588⟩ (batchDecodedStack I rest) mem aw rdata acc k C) :
    RDrev runtimeBytecode g s0 ∨
      ((if calldataWord I.calldata 196 = ⟨0⟩ then calldataWord I.calldata 164 = ⟨0⟩
        else calldataWord I.calldata 164 ≠ ⟨0⟩ ∧
          UInt256.ofNat I.codeOwner.val ≠ calldataWord I.calldata 164) ∧
       ∃ k' C', RD runtimeBytecode I g s0 ⟨660⟩ (batchDecodedStack I rest) mem aw rdata acc k' C') := by
  rcases batch_bytecode_withdrawal_owner_cases rest space canonical reached with ⟨rejected, _⟩ | accepted
  · exact Or.inl rejected
  · exact Or.inr accepted

end Rollup.EVM
