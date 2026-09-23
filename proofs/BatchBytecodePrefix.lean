import proofs.BatchBytecodeHeader

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Rollup.EVM

/-- Checks made before a batch can change credit. -/
structure BatchPrefixChecks (accounts : AccountMap) (env : ExecutionEnv) : Prop where
  nonpayable : env.weiValue = ⟨0⟩
  length : 228 ≤ env.calldata.size
  signedBound : env.calldata.size < 2 ^ 255 + 4
  depositCanonical : (calldataWord env.calldata 100).toNat < _root_.EVM.addressModulus
  withdrawalCanonical : (calldataWord env.calldata 164).toNat < _root_.EVM.addressModulus
  unlocked : solcSlotWord accounts env ⟨6⟩ = ⟨0⟩
  authorized : UInt256.ofNat env.source.val = UInt256.land (solcSlotWord accounts env ⟨0⟩) solcAddrMask
  numberFits : (solcSlotWord accounts env ⟨2⟩).toNat + 1 < UInt256.size
  nextNumber : (calldataWord env.calldata 4).toNat = (solcSlotWord accounts env ⟨2⟩).toNat + 1
  oldRoot : calldataWord env.calldata 36 = solcSlotWord accounts env ⟨1⟩

/-- A batch rejects or reaches the owner checks with its header checked. -/
theorem batch_bytecode_prefix {cA gh bl σ σ₀ A I} {g : Sat256}
    (code : I.code = runtimeBytecode) (writable : I.perm = true)
    (bounded : I.calldata.size < UInt256.size)
    (selector : solcSelectorWord I = ⟨0x88af9950⟩) :
    RDrev runtimeBytecode g (initState cA gh bl σ σ₀ g A I) ∨
      (BatchPrefixChecks σ I ∧
       ∃ k C, RD runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨516⟩
         (batchDecodedStack I [⟨226⟩, ⟨0x88af9950⟩])
         solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
         (cA, sstoreAccountMap I.codeOwner σ ⟨6⟩ ⟨1⟩) k C) := by
  rcases batch_entry_classification (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (g := g) code bounded selector with
    rejected | ⟨value, length, signedBound, depositCanonical, withdrawalCanonical, _, _, entered⟩
  · exact Or.inl rejected
  · by_cases unlocked : solcSlotWord σ I ⟨6⟩ = ⟨0⟩
    · obtain ⟨_, _, locked⟩ := batch_bytecode_enter _ (by simp [batchDecodedStack]) writable unlocked entered
      rcases batch_bytecode_authorization _ (by simp [batchDecodedStack]) locked with
        rejected | ⟨authorized, _, _, reached⟩
      · exact Or.inl rejected
      · rcases batch_bytecode_header _ (by decide) reached with
          rejected | ⟨fits, number, root, finished⟩
        · exact Or.inl rejected
        · rw [solc_slot_store_other σ I ⟨0⟩ ⟨6⟩ ⟨1⟩ (by decide)] at authorized
          rw [solc_slot_store_other σ I ⟨2⟩ ⟨6⟩ ⟨1⟩ (by decide)] at fits number
          rw [solc_slot_store_other σ I ⟨1⟩ ⟨6⟩ ⟨1⟩ (by decide)] at root
          have numberNat : (calldataWord I.calldata 4).toNat = (solcSlotWord σ I ⟨2⟩).toNat + 1 := by
            rw [number, uadd_toNat]
            change ((solcSlotWord σ I ⟨2⟩).toNat + 1) % UInt256.size =
              (solcSlotWord σ I ⟨2⟩).toNat + 1
            exact Nat.mod_eq_of_lt fits
          exact Or.inr ⟨⟨value, length, signedBound, depositCanonical, withdrawalCanonical,
            unlocked, authorized, fits, numberNat, root⟩, finished⟩
    · exact Or.inl (batch_bytecode_locked _ (by simp [batchDecodedStack]) unlocked entered)

/-- Accepted batches satisfy authorization, number continuity, and root continuity. -/
theorem batch_xi_header {cA gh bl σ σ₀ A I} {g : Sat256}
    {cA' σ' gas substate output} (code : I.code = runtimeBytecode)
    (writable : I.perm = true) (bounded : I.calldata.size < UInt256.size)
    (selector : solcSelectorWord I = ⟨0x88af9950⟩)
    (success : Ξ cA gh bl σ σ₀ g.toUInt256 A I = .ok (.success (cA', σ', gas, substate) output)) :
    BatchPrefixChecks σ I := by
  rcases batch_bytecode_prefix (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (g := g) code writable bounded selector with
    rejected | ⟨checks, _⟩
  · rcases rejected.xiResult code with failed | ⟨gas', data, actual⟩
    · rw [success] at failed
      cases failed
    · rw [success] at actual
      cases actual
  · exact checks

end Rollup.EVM
