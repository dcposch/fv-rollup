import proofs.RuntimeBytecode

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Rollup.EVM

/-- The subtract routine returns the difference when the debit is covered. -/
theorem runtime_checked_subtract {I : ExecutionEnv} {g : Sat256} {s0 : Ethereum.State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (a b ret : UInt256) (rest : List UInt256) (space : rest.length + 6 ≤ 1024)
    (covered : b.toNat ≤ a.toNat)
    (destination : (D_J runtimeBytecode 0).contains ret = true)
    (reached : RD runtimeBytecode I g s0 ⟨1410⟩ (a :: b :: ret :: rest)
      mem aw rdata acc k C) :
    ∃ k' C', RD runtimeBytecode I g s0 ret (UInt256.sub a b :: rest) mem aw rdata acc k' C' := by
  have compare : UInt256.gt (UInt256.sub a b) a = ⟨0⟩ := ugt_zero (by rw [usub_toNat covered]; omega)
  have guard := runtime_run reached with [jumpdest, dup2, dup2, sub, dup2, dup2,
    gt, iszero, push2 ⟨1404⟩]
  rw [compare] at guard
  exact ⟨_, _, runtime_run guard with [jumpiT (by decide)
    (jumpScan_valid runtimeBytecode 1404 1420 (by decide +kernel)),
    jumpdest, swap3, swap2, pop, pop, jump destination]⟩

end Rollup.EVM
