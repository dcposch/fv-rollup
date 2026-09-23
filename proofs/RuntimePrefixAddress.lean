import proofs.RuntimePrefixDispatch

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Rollup.EVM

/-- The address check returns only for a canonical 160-bit word. -/
theorem runtime_prefix_address_check {I : ExecutionEnv} {target child : Ethereum.State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (word ret : UInt256) (rest : List UInt256)
    (canonical : word.toNat < _root_.EVM.addressModulus)
    (destination : (D_J runtimeBytecode 0).contains ret = true)
    (space : rest.length + 6 ≤ 1024)
    (reached : PCR runtimeBytecode I target child ⟨1165⟩ (word :: ret :: rest) mem aw rdata acc) :
    PCR runtimeBytecode I target child ret rest mem aw rdata acc := by
  have mask : UInt256.sub (UInt256.shiftLeft ⟨1⟩ ⟨160⟩) ⟨1⟩ = solcAddrMask := by decide
  have guard := runtime_run reached with [jumpdest, push1 ⟨1⟩, push1 ⟨1⟩,
    push1 ⟨160⟩, shl, sub, dup2, and, dup2, eq, push2 ⟨1185⟩]
  rw [mask, solcAddrCanon_eq canonical] at guard
  exact runtime_run guard with [
    jumpiT (by decide) (jumpScan_valid runtimeBytecode 1185 1200 (by decide +kernel)),
    jumpdest, pop, jump destination]

/-- A word with nonzero high address bits fails the address check. -/
theorem runtime_prefix_address_check_reject {I : ExecutionEnv} {target child : Ethereum.State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (word ret : UInt256) (rest : List UInt256)
    (noncanonical : ¬ word.toNat < _root_.EVM.addressModulus)
    (space : rest.length + 6 ≤ 1024)
    (reached : PCR runtimeBytecode I target child ⟨1165⟩ (word :: ret :: rest) mem aw rdata acc) :
    False := by
  have mask : UInt256.sub (UInt256.shiftLeft ⟨1⟩ ⟨160⟩) ⟨1⟩ = solcAddrMask := by decide
  have different : word ≠ UInt256.land word solcAddrMask := by
    intro same
    have smaller := solcAddrMask_result_canonical word
    rw [← same] at smaller
    exact noncanonical smaller
  have guard := runtime_run reached with [jumpdest, push1 ⟨1⟩, push1 ⟨1⟩,
    push1 ⟨160⟩, shl, sub, dup2, and, dup2, eq, push2 ⟨1185⟩]
  rw [mask, u256_eq_of_ne different] at guard
  have rejected := runtime_run guard with [jumpiNT rfl, push0, dup1]
  exact rejected.halt (arg := none) (by decide +kernel) (Or.inr (Or.inr (Or.inl rfl)))

end Rollup.EVM
