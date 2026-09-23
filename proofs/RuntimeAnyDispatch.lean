import proofs.RuntimeScalarGetter

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Rollup.EVM

inductive RuntimeEntry where
  | sequencer | batch | stateRoot | batchNumber | withdrawal | backing
  | pendingDeposits | deposit | pendingWithdrawals

def runtimeEntryPC : RuntimeEntry → UInt256
  | .sequencer => ⟨136⟩
  | .batch => ⟨195⟩
  | .stateRoot => ⟨228⟩
  | .batchNumber => ⟨263⟩
  | .withdrawal => ⟨284⟩
  | .backing => ⟨315⟩
  | .pendingDeposits => ⟨336⟩
  | .deposit => ⟨379⟩
  | .pendingWithdrawals => ⟨398⟩

def runtimeEntrySelector : RuntimeEntry → UInt256
  | .sequencer => ⟨0x5c1bba38⟩
  | .batch => ⟨0x88af9950⟩
  | .stateRoot => ⟨0x9588eca2⟩
  | .batchNumber => ⟨0xba873065⟩
  | .withdrawal => ⟨0xbb3ef682⟩
  | .backing => ⟨0xc9503fe2⟩
  | .pendingDeposits => ⟨0xeb3349b9⟩
  | .deposit => ⟨0xf340fa01⟩
  | .pendingWithdrawals => ⟨0xf3f43703⟩

/-- Dispatch rejects or reaches a known entry, without a calldata-size premise. -/
theorem runtime_dispatch_any {cA gh bl σ σ₀ A I} {g : Sat256}
    (code : I.code = runtimeBytecode) :
    RDrev runtimeBytecode g (initState cA gh bl σ σ₀ g A I) ∨
      ∃ entry k C, RD runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) (runtimeEntryPC entry)
        [runtimeEntrySelector entry] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have entered := runtime_prologue (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (g := g) code
  have sizeGuard := runtime_run entered with [push1 ⟨4⟩, calldatasize, lt, push2 ⟨132⟩]
  by_cases length : UInt256.lt (UInt256.ofNat I.calldata.size) ⟨4⟩ = ⟨0⟩
  · have loaded := runtime_run sizeGuard with [jumpiNT length, push0, calldataload, push1 ⟨224⟩, shr]
    have compared := runtime_run loaded with [dup1, push4 ⟨0xbb3ef682⟩, gt, push2 ⟨87⟩]
    by_cases right : UInt256.gt ⟨0xbb3ef682⟩ (solcSelectorWord I) = ⟨0⟩
    · have split := runtime_run compared with [jumpiNT right]
      have guard0 := runtime_run split with [dup1, push4 ⟨0xbb3ef682⟩, eq, push2 ⟨284⟩]
      by_cases miss0 : UInt256.eq ⟨0xbb3ef682⟩ (solcSelectorWord I) = ⟨0⟩
      · have next0 := runtime_run guard0 with [jumpiNT miss0]
        have guard0 := runtime_run next0 with [dup1, push4 ⟨0xc9503fe2⟩, eq, push2 ⟨315⟩]
        by_cases miss0 : UInt256.eq ⟨0xc9503fe2⟩ (solcSelectorWord I) = ⟨0⟩
        · have next0 := runtime_run guard0 with [jumpiNT miss0]
          have guard0 := runtime_run next0 with [dup1, push4 ⟨0xeb3349b9⟩, eq, push2 ⟨336⟩]
          by_cases miss0 : UInt256.eq ⟨0xeb3349b9⟩ (solcSelectorWord I) = ⟨0⟩
          · have next0 := runtime_run guard0 with [jumpiNT miss0]
            have guard0 := runtime_run next0 with [dup1, push4 ⟨0xf340fa01⟩, eq, push2 ⟨379⟩]
            by_cases miss0 : UInt256.eq ⟨0xf340fa01⟩ (solcSelectorWord I) = ⟨0⟩
            · have next0 := runtime_run guard0 with [jumpiNT miss0]
              have guard0 := runtime_run next0 with [dup1, push4 ⟨0xf3f43703⟩, eq, push2 ⟨398⟩]
              by_cases miss0 : UInt256.eq ⟨0xf3f43703⟩ (solcSelectorWord I) = ⟨0⟩
              · have next0 := runtime_run guard0 with [jumpiNT miss0]
                have rejected := runtime_run next0 with [push0, dup1]
                exact .inl (rejected.rev 0 (by decide +kernel)
                  (fun s _ stack => memExpRevert0 s stack) (by evm_ov))
              · have same : solcSelectorWord I = ⟨0xf3f43703⟩ := by
                  by_contra ne
                  exact miss0 (u256_eq_of_ne (Ne.symm ne))
                change RD runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) _
                  [⟨398⟩, UInt256.eq ⟨0xf3f43703⟩ (solcSelectorWord I), solcSelectorWord I] _ _ _ _ _ _ at guard0
                rw [same] at guard0
                exact .inr ⟨.pendingWithdrawals, _, _, runtime_run guard0 with [jumpiT (by decide +kernel)
                  (jumpScan_valid runtimeBytecode 398 433 (by decide +kernel))]⟩
            · have same : solcSelectorWord I = ⟨0xf340fa01⟩ := by
                by_contra ne
                exact miss0 (u256_eq_of_ne (Ne.symm ne))
              change RD runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) _
                [⟨379⟩, UInt256.eq ⟨0xf340fa01⟩ (solcSelectorWord I), solcSelectorWord I] _ _ _ _ _ _ at guard0
              rw [same] at guard0
              exact .inr ⟨.deposit, _, _, runtime_run guard0 with [jumpiT (by decide +kernel)
                (jumpScan_valid runtimeBytecode 379 414 (by decide +kernel))]⟩
          · have same : solcSelectorWord I = ⟨0xeb3349b9⟩ := by
              by_contra ne
              exact miss0 (u256_eq_of_ne (Ne.symm ne))
            change RD runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) _
              [⟨336⟩, UInt256.eq ⟨0xeb3349b9⟩ (solcSelectorWord I), solcSelectorWord I] _ _ _ _ _ _ at guard0
            rw [same] at guard0
            exact .inr ⟨.pendingDeposits, _, _, runtime_run guard0 with [jumpiT (by decide +kernel)
              (jumpScan_valid runtimeBytecode 336 371 (by decide +kernel))]⟩
        · have same : solcSelectorWord I = ⟨0xc9503fe2⟩ := by
            by_contra ne
            exact miss0 (u256_eq_of_ne (Ne.symm ne))
          change RD runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) _
            [⟨315⟩, UInt256.eq ⟨0xc9503fe2⟩ (solcSelectorWord I), solcSelectorWord I] _ _ _ _ _ _ at guard0
          rw [same] at guard0
          exact .inr ⟨.backing, _, _, runtime_run guard0 with [jumpiT (by decide +kernel)
            (jumpScan_valid runtimeBytecode 315 350 (by decide +kernel))]⟩
      · have same : solcSelectorWord I = ⟨0xbb3ef682⟩ := by
          by_contra ne
          exact miss0 (u256_eq_of_ne (Ne.symm ne))
        change RD runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) _
          [⟨284⟩, UInt256.eq ⟨0xbb3ef682⟩ (solcSelectorWord I), solcSelectorWord I] _ _ _ _ _ _ at guard0
        rw [same] at guard0
        exact .inr ⟨.withdrawal, _, _, runtime_run guard0 with [jumpiT (by decide +kernel)
          (jumpScan_valid runtimeBytecode 284 319 (by decide +kernel))]⟩
    · have split := runtime_run compared with [jumpiT right
        (jumpScan_valid runtimeBytecode 87 140 (by decide +kernel)), jumpdest]
      have guard0 := runtime_run split with [dup1, push4 ⟨0x5c1bba38⟩, eq, push2 ⟨136⟩]
      by_cases miss0 : UInt256.eq ⟨0x5c1bba38⟩ (solcSelectorWord I) = ⟨0⟩
      · have next0 := runtime_run guard0 with [jumpiNT miss0]
        have guard0 := runtime_run next0 with [dup1, push4 ⟨0x88af9950⟩, eq, push2 ⟨195⟩]
        by_cases miss0 : UInt256.eq ⟨0x88af9950⟩ (solcSelectorWord I) = ⟨0⟩
        · have next0 := runtime_run guard0 with [jumpiNT miss0]
          have guard0 := runtime_run next0 with [dup1, push4 ⟨0x9588eca2⟩, eq, push2 ⟨228⟩]
          by_cases miss0 : UInt256.eq ⟨0x9588eca2⟩ (solcSelectorWord I) = ⟨0⟩
          · have next0 := runtime_run guard0 with [jumpiNT miss0]
            have guard0 := runtime_run next0 with [dup1, push4 ⟨0xba873065⟩, eq, push2 ⟨263⟩]
            by_cases miss0 : UInt256.eq ⟨0xba873065⟩ (solcSelectorWord I) = ⟨0⟩
            · have next0 := runtime_run guard0 with [jumpiNT miss0]
              have rejected := runtime_run next0 with [jumpdest, push0, dup1]
              exact .inl (rejected.rev 0 (by decide +kernel)
                (fun s _ stack => memExpRevert0 s stack) (by evm_ov))
            · have same : solcSelectorWord I = ⟨0xba873065⟩ := by
                by_contra ne
                exact miss0 (u256_eq_of_ne (Ne.symm ne))
              change RD runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) _
                [⟨263⟩, UInt256.eq ⟨0xba873065⟩ (solcSelectorWord I), solcSelectorWord I] _ _ _ _ _ _ at guard0
              rw [same] at guard0
              exact .inr ⟨.batchNumber, _, _, runtime_run guard0 with [jumpiT (by decide +kernel)
                (jumpScan_valid runtimeBytecode 263 298 (by decide +kernel))]⟩
          · have same : solcSelectorWord I = ⟨0x9588eca2⟩ := by
              by_contra ne
              exact miss0 (u256_eq_of_ne (Ne.symm ne))
            change RD runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) _
              [⟨228⟩, UInt256.eq ⟨0x9588eca2⟩ (solcSelectorWord I), solcSelectorWord I] _ _ _ _ _ _ at guard0
            rw [same] at guard0
            exact .inr ⟨.stateRoot, _, _, runtime_run guard0 with [jumpiT (by decide +kernel)
              (jumpScan_valid runtimeBytecode 228 263 (by decide +kernel))]⟩
        · have same : solcSelectorWord I = ⟨0x88af9950⟩ := by
            by_contra ne
            exact miss0 (u256_eq_of_ne (Ne.symm ne))
          change RD runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) _
            [⟨195⟩, UInt256.eq ⟨0x88af9950⟩ (solcSelectorWord I), solcSelectorWord I] _ _ _ _ _ _ at guard0
          rw [same] at guard0
          exact .inr ⟨.batch, _, _, runtime_run guard0 with [jumpiT (by decide +kernel)
            (jumpScan_valid runtimeBytecode 195 230 (by decide +kernel))]⟩
      · have same : solcSelectorWord I = ⟨0x5c1bba38⟩ := by
          by_contra ne
          exact miss0 (u256_eq_of_ne (Ne.symm ne))
        change RD runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) _
          [⟨136⟩, UInt256.eq ⟨0x5c1bba38⟩ (solcSelectorWord I), solcSelectorWord I] _ _ _ _ _ _ at guard0
        rw [same] at guard0
        exact .inr ⟨.sequencer, _, _, runtime_run guard0 with [jumpiT (by decide +kernel)
          (jumpScan_valid runtimeBytecode 136 171 (by decide +kernel))]⟩
  · have rejected := runtime_run sizeGuard with [jumpiT length
      (jumpScan_valid runtimeBytecode 132 140 (by decide +kernel)), jumpdest, push0, dup1]
    exact .inl (rejected.rev 0 (by decide +kernel)
      (fun s _ stack => memExpRevert0 s stack) (by evm_ov))

end Rollup.EVM
