import proofs.BatchEntry
import Reasoning.Storage

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Rollup.EVM

/-- A storage write preserves each other word. -/
theorem solc_slot_store_other (accounts : AccountMap) (env : ExecutionEnv)
    (readSlot writeSlot value : UInt256) (different : readSlot ≠ writeSlot) :
    solcSlotWord (sstoreAccountMap env.codeOwner accounts writeSlot value) env readSlot =
      solcSlotWord accounts env readSlot := by
  have preserved := storageLoad_storageStore_ne
    ({ (default : Ethereum.State) with accountMap := accounts }) env.codeOwner
    different (val := value)
  simpa only [Solm.EVM.storageLoad, Ethereum.State.lookupAccount, storageStore_accountMap]
    using preserved

/-- The batch caller must match the address in slot zero. -/
theorem batch_bytecode_authorization_cases {I : ExecutionEnv} {g : Sat256} {s0 : Ethereum.State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : Nat}
    (stack : List UInt256) (space : stack.length + 4 ≤ 1024)
    (reached : RD runtimeBytecode I g s0 ⟨459⟩ stack mem aw rdata (cA, σ) k C) :
    (RDrev runtimeBytecode g s0 ∧ ¬(UInt256.ofNat I.source.val = UInt256.land (solcSlotWord σ I ⟨0⟩) solcAddrMask)) ∨
      (UInt256.ofNat I.source.val = UInt256.land (solcSlotWord σ I ⟨0⟩) solcAddrMask ∧
       ∃ k' C', RD runtimeBytecode I g s0 ⟨479⟩ stack mem aw rdata (cA, σ) k' C') := by
  have slot := runtime_run reached with [push0]
  obtain ⟨_, _, loaded⟩ := slot.sload (by decide +kernel) (by evm_ov)
  have guard := runtime_run loaded with [push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩,
    shl, sub, and, caller, eq, push2 ⟨479⟩]
  have mask : UInt256.sub (UInt256.shiftLeft ⟨1⟩ ⟨160⟩) ⟨1⟩ = solcAddrMask := by decide
  rw [mask, u256_land_comm solcAddrMask] at guard
  by_cases authorized : UInt256.ofNat I.source.val = UInt256.land (solcSlotWord σ I ⟨0⟩) solcAddrMask
  · rw [authorized, u256_eq_refl] at guard
    exact Or.inr ⟨authorized, _, _, runtime_run guard with [jumpiT (by decide)
      (jumpScan_valid runtimeBytecode 479 510 (by decide +kernel))]⟩
  · rw [u256_eq_of_ne authorized] at guard
    have rejected := runtime_run guard with [jumpiNT rfl, push0, dup1]
    exact Or.inl ⟨(rejected.rev 0 (by decide +kernel)
      (fun s _ items => memExpRevert0 s items) (by evm_ov)), by exact authorized⟩

/-- Discard the reason for rejection. -/
theorem batch_bytecode_authorization {I : ExecutionEnv} {g : Sat256} {s0 : Ethereum.State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : Nat}
    (stack : List UInt256) (space : stack.length + 4 ≤ 1024)
    (reached : RD runtimeBytecode I g s0 ⟨459⟩ stack mem aw rdata (cA, σ) k C) :
    RDrev runtimeBytecode g s0 ∨
      (UInt256.ofNat I.source.val = UInt256.land (solcSlotWord σ I ⟨0⟩) solcAddrMask ∧
       ∃ k' C', RD runtimeBytecode I g s0 ⟨479⟩ stack mem aw rdata (cA, σ) k' C') := by
  rcases batch_bytecode_authorization_cases stack space reached with ⟨rejected, _⟩ | accepted
  · exact Or.inl rejected
  · exact Or.inr accepted

/-- An accepted writable batch binds authorization to the actual EVM caller. -/
theorem batch_xi_authorized {cA gh bl σ σ₀ A I} {g : Sat256}
    {cA' σ' gas substate output} (code : I.code = runtimeBytecode)
    (writable : I.perm = true) (bounded : I.calldata.size < UInt256.size)
    (selector : solcSelectorWord I = ⟨0x88af9950⟩)
    (success : Ξ cA gh bl σ σ₀ g.toUInt256 A I = .ok (.success (cA', σ', gas, substate) output)) :
    UInt256.ofNat I.source.val = UInt256.land (solcSlotWord σ I ⟨0⟩) solcAddrMask := by
  have notRejected (rejected : RDrev runtimeBytecode g (initState cA gh bl σ σ₀ g A I)) : False := by
    rcases rejected.xiResult code with failed | ⟨gas', data, actual⟩
    · rw [success] at failed
      cases failed
    · rw [success] at actual
      cases actual
  rcases batch_entry_classification (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (g := g) code bounded selector with
    rejected | ⟨_, _, _, _, _, _, _, reached⟩
  · exact False.elim (notRejected rejected)
  · have unlocked := (batch_xi_entry_checks code bounded selector success).2.2.2.2.2
    obtain ⟨_, _, acquired⟩ := batch_bytecode_enter _ (by simp [batchDecodedStack]) writable unlocked reached
    rcases batch_bytecode_authorization _ (by simp [batchDecodedStack]) acquired with
      rejected | ⟨authorized, _⟩
    · exact False.elim (notRejected rejected)
    · rw [solc_slot_store_other σ I ⟨0⟩ ⟨6⟩ ⟨1⟩ (by decide)] at authorized
      exact authorized

end Rollup.EVM
