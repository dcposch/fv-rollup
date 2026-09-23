import semantics.Bytecode
import proofs.BytecodeSteps
import Reasoning.Solc

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Rollup.EVM

open Lean in
macro "runtime_run " base:term " with " "[" steps:evmStep,* "]" : term => do
  let mut acc := base
  for step in steps.getElems do
    match step with
    | `(evmStep| raw $op:ident $args*) => acc ← `($(acc).$op $args*)
    | `(evmStep| $op:ident $args*) =>
      match op.getId with
      | `jump => acc ← `($(acc).jump (by decide +kernel) $(args[0]!) (by evm_ov))
      | `jumpiT => acc ← `($(acc).jumpiT (by decide +kernel) $(args[0]!) $(args[1]!) (by evm_ov))
      | `jumpiNT => acc ← `($(acc).jumpiNT (by decide +kernel) $(args[0]!) (by evm_ov))
      | _ => acc ← `($(acc).$op $args* (by decide +kernel) (by evm_ov))
    | _ => Macro.throwUnsupported
  return acc

/-- The runtime starts by setting the free memory pointer. -/
theorem runtime_prologue {cA gh bl σ σ₀ A I} {g : Sat256}
    (code : I.code = runtimeBytecode) :
    RD runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5⟩ []
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) 3 18 := by
  have start := RD.initState (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (g := g) code
  exact (runtime_run start with [push1 ⟨128⟩, push1 ⟨64⟩]).mstore 9
    solcFreePtrMem (UInt256.ofNat 3) (by decide +kernel) mem_cost rfl (by decide +kernel) (by decide +kernel)

/-- Calls with fewer than four calldata bytes revert or run out of gas. -/
theorem runtime_short_calldata {cA gh bl σ σ₀ A I} {g : Sat256}
    (code : I.code = runtimeBytecode) (short : I.calldata.size < 4) :
    RDrev runtimeBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have entered := runtime_prologue (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (g := g) code
  have guard := runtime_run entered with [push1 ⟨4⟩, calldatasize, lt, push2 ⟨132⟩,
    jumpiT (lt_four_ne_zero_of_lt short) (jumpScan_valid runtimeBytecode 132 140 (by decide +kernel)),
    jumpdest, push0, dup1]
  exact guard.rev 0 (by decide +kernel) (fun s _ stack => memExpRevert0 s stack) (by evm_ov)

/-- Load the selector without changing accounts. -/
theorem runtime_selector {cA gh bl σ σ₀ A I} {g : Sat256}
    (code : I.code = runtimeBytecode) (length : 4 ≤ I.calldata.size)
    (bounded : I.calldata.size < UInt256.size) :
    ∃ k C, RD runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨18⟩
      [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have entered := runtime_prologue (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (g := g) code
  have guard := runtime_run entered with [push1 ⟨4⟩, calldatasize, lt, push2 ⟨132⟩,
    jumpiNT (lt_four_eq_zero_of_ge length bounded)]
  exact ⟨_, _, runtime_run guard with [push0, calldataload, push1 ⟨224⟩, shr]⟩

/-- The deposit selector reaches the payable deposit decoder. -/
theorem runtime_deposit_dispatch {cA gh bl σ σ₀ A I} {g : Sat256}
    (code : I.code = runtimeBytecode) (length : 4 ≤ I.calldata.size)
    (bounded : I.calldata.size < UInt256.size)
    (selector : solcSelectorWord I = ⟨0xf340fa01⟩) :
    ∃ k C, RD runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1331⟩
      [⟨4⟩, UInt256.ofNat I.calldata.size, ⟨393⟩, ⟨226⟩, ⟨0xf340fa01⟩]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, loaded⟩ := runtime_selector (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) code length bounded
  rw [selector] at loaded
  have split := runtime_run loaded with [dup1, push4 ⟨0xbb3ef682⟩, gt, push2 ⟨87⟩,
    jumpiNT (by decide +kernel)]
  have first := runtime_run split with [dup1, push4 ⟨0xbb3ef682⟩, eq, push2 ⟨284⟩,
    jumpiNT (by decide +kernel)]
  have second := runtime_run first with [dup1, push4 ⟨0xc9503fe2⟩, eq, push2 ⟨315⟩,
    jumpiNT (by decide +kernel)]
  have third := runtime_run second with [dup1, push4 ⟨0xeb3349b9⟩, eq, push2 ⟨336⟩,
    jumpiNT (by decide +kernel)]
  have found := runtime_run third with [dup1, push4 ⟨0xf340fa01⟩, eq, push2 ⟨379⟩,
    jumpiT (by decide +kernel) (jumpScan_valid runtimeBytecode 379 400 (by decide +kernel)),
    jumpdest, push2 ⟨226⟩, push2 ⟨393⟩, calldatasize, push1 ⟨4⟩, push2 ⟨1331⟩]
  exact ⟨_, _, runtime_run found with [jump (jumpScan_valid runtimeBytecode 1331 1350 (by decide +kernel))]⟩

end Rollup.EVM
