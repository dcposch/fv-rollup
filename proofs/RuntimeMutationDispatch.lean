import proofs.RuntimeScalarGetter

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Rollup.EVM

inductive Mutation where
  | batch | withdrawal

def mutationEntry : Mutation → UInt256
  | .batch => ⟨195⟩
  | .withdrawal => ⟨284⟩

def mutationSelector : Mutation → UInt256
  | .batch => ⟨0x88af9950⟩
  | .withdrawal => ⟨0xbb3ef682⟩

def mutationDecoder : Mutation → UInt256
  | .batch => ⟨1188⟩
  | .withdrawal => ⟨1289⟩

/-- Each mutating selector reaches its nonpayable guard. -/
theorem mutation_dispatch {cA gh bl σ σ₀ A I} {g : Sat256}
    (mutation : Mutation) (code : I.code = runtimeBytecode)
    (length : 4 ≤ I.calldata.size) (bounded : I.calldata.size < UInt256.size)
    (selector : solcSelectorWord I = mutationSelector mutation) :
    ∃ k C, RD runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) (mutationEntry mutation)
      [mutationSelector mutation] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, loaded⟩ := runtime_selector (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) code length bounded
  rw [selector] at loaded
  cases mutation with
  | batch =>
    have split := runtime_run loaded with [dup1, push4 ⟨0xbb3ef682⟩, gt, push2 ⟨87⟩,
      jumpiT (by decide +kernel) (jumpScan_valid runtimeBytecode 87 140 (by decide +kernel)), jumpdest]
    have first := runtime_run split with [dup1, push4 ⟨0x5c1bba38⟩, eq, push2 ⟨136⟩,
      jumpiNT (by decide +kernel)]
    exact ⟨_, _, runtime_run first with [dup1, push4 ⟨0x88af9950⟩, eq, push2 ⟨195⟩,
      jumpiT (by decide +kernel) (jumpScan_valid runtimeBytecode 195 320 (by decide +kernel))]⟩
  | withdrawal =>
    have split := runtime_run loaded with [dup1, push4 ⟨0xbb3ef682⟩, gt, push2 ⟨87⟩,
      jumpiNT (by decide +kernel)]
    exact ⟨_, _, runtime_run split with [dup1, push4 ⟨0xbb3ef682⟩, eq, push2 ⟨284⟩,
      jumpiT (by decide +kernel) (jumpScan_valid runtimeBytecode 284 320 (by decide +kernel))]⟩

private theorem mutation_guard_destination (mutation : Mutation) :
    (D_J runtimeBytecode 0).contains (mutationEntry mutation + ⟨11⟩) = true := by
  cases mutation with
  | batch => exact jumpScan_valid runtimeBytecode 206 320 (by decide +kernel)
  | withdrawal => exact jumpScan_valid runtimeBytecode 295 320 (by decide +kernel)

private theorem mutation_decoder_destination (mutation : Mutation) :
    (D_J runtimeBytecode 0).contains (mutationDecoder mutation) = true := by
  cases mutation with
  | batch => exact jumpScan_valid runtimeBytecode 1188 1310 (by decide +kernel)
  | withdrawal => exact jumpScan_valid runtimeBytecode 1289 1310 (by decide +kernel)

/-- Batches and withdrawals reject nonzero call value. -/
theorem mutation_nonpayable {I : ExecutionEnv} {g : Sat256} {s0 : Ethereum.State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (mutation : Mutation) (rest : List UInt256) (space : rest.length + 3 ≤ 1024)
    (value : I.weiValue ≠ ⟨0⟩)
    (reached : RD runtimeBytecode I g s0 (mutationEntry mutation) rest mem aw rdata acc k C) :
    RDrev runtimeBytecode g s0 := by
  have guard := runtime_cases_run mutation from reached with [jumpdest, callvalue, dup1, iszero,
    push2 (mutationEntry mutation + ⟨11⟩)]
  have rejected := runtime_cases_run mutation from guard with [jumpiNT (isZero_eq_zero_of_ne value), push0, dup1]
  exact rejected.rev 0 (by cases mutation <;> decide +kernel)
    (fun s _ stack => memExpRevert0 s stack) (by evm_ov)

/-- Zero-value batches and withdrawals enter their argument decoders. -/
theorem mutation_decoder {I : ExecutionEnv} {g : Sat256} {s0 : Ethereum.State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (mutation : Mutation) (rest : List UInt256) (space : rest.length + 5 ≤ 1024)
    (value : I.weiValue = ⟨0⟩)
    (reached : RD runtimeBytecode I g s0 (mutationEntry mutation) rest mem aw rdata acc k C) :
    ∃ k' C', RD runtimeBytecode I g s0 (mutationDecoder mutation)
      (⟨4⟩ :: UInt256.ofNat I.calldata.size :: (mutationEntry mutation + ⟨26⟩) :: ⟨226⟩ :: rest)
      mem aw rdata acc k' C' := by
  have guard := runtime_cases_run mutation from reached with [jumpdest, callvalue, dup1, iszero,
    push2 (mutationEntry mutation + ⟨11⟩)]
  exact ⟨_, _, runtime_cases_run mutation from guard with [
    jumpiT (by rw [value]; decide) (mutation_guard_destination mutation), jumpdest, pop,
    push2 ⟨226⟩, push2 (mutationEntry mutation + ⟨26⟩), calldatasize, push1 ⟨4⟩,
    push2 (mutationDecoder mutation), jump (mutation_decoder_destination mutation)]⟩

end Rollup.EVM
