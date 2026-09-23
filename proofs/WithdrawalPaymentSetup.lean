import proofs.WithdrawalBytecodeChecks

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Rollup.EVM

/-- The CALL stack contains the decoded owner and amount, with empty input and output areas. -/
theorem withdrawal_bytecode_payment_setup {I : ExecutionEnv} {g : Sat256} {s0 : Ethereum.State}
    {mem : ByteArray} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (credit : UInt256) (rest : List UInt256) (space : rest.length + 15 ≤ 1024)
    (canonical : (calldataWord I.calldata 4).toNat < _root_.EVM.addressModulus)
    (memorySize : mem.size = 96)
    (freePointer : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (reached : RD runtimeBytecode I g s0 ⟨908⟩
      (credit :: calldataWord I.calldata 36 :: calldataWord I.calldata 4 :: rest)
      mem (UInt256.ofNat 3) rdata acc k C) :
    ∃ gasArg k' C', RD runtimeBytecode I g s0 ⟨935⟩
      (gasArg :: calldataWord I.calldata 4 :: calldataWord I.calldata 36 ::
        ⟨128⟩ :: ⟨0⟩ :: ⟨128⟩ :: ⟨0⟩ ::
        ⟨128⟩ :: calldataWord I.calldata 36 :: calldataWord I.calldata 4 :: ⟨0⟩ ::
        credit :: calldataWord I.calldata 36 :: calldataWord I.calldata 4 :: rest)
      mem (UInt256.ofNat 3) rdata acc k' C' := by
  have mask : UInt256.sub (UInt256.shiftLeft ⟨1⟩ ⟨160⟩) ⟨1⟩ = solcAddrMask := by decide
  have cleaned := runtime_run reached with [jumpdest, push0, dup4,
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, and]
  rw [mask, solcAddrMask_clean_left canonical] at cleaned
  have first := runtime_run cleaned with [dup4, push1 ⟨64⟩]
  have loaded := first.mload 0 ⟨128⟩ (UInt256.ofNat 3)
    (by decide +kernel) mem_cost
    (mloadFreePtrValue (by rw [memorySize]; decide) (by decide) freePointer)
    (by decide) (by evm_ov)
  have second := runtime_run loaded with [push0, push1 ⟨64⟩]
  have loadedAgain := second.mload 0 ⟨128⟩ (UInt256.ofNat 3)
    (by decide +kernel) mem_cost
    (mloadFreePtrValue (by rw [memorySize]; decide) (by decide) freePointer)
    (by decide) (by evm_ov)
  have beforeGas := runtime_run loadedAgain with [dup1, dup4, sub, dup2, dup6, dup8]
  obtain ⟨gasArg, ready⟩ := beforeGas.gas (by decide +kernel) (by evm_ov)
  exact ⟨gasArg, _, _, ready⟩

end Rollup.EVM
