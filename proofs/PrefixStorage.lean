import proofs.PrefixReach

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Rollup.EVM

theorem PCR.sload {code : ByteArray} {ee : ExecutionEnv} {target child : Ethereum.State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {a : UInt256} {t : List UInt256}
    (h : PCR code ee target child pc (a :: t) mem aw rdata (cA, σ))
    (hdec : decode code pc = some (.SLOAD, .none)) (hov : t.length + 1 ≤ 1024) :
    PCR code ee target child (pc + ⟨1⟩)
      ((σ.find? ee.codeOwner |>.option ⟨0⟩ (fun ac => ac.storage.findD a ⟨0⟩)) :: t)
      mem aw rdata (cA, σ) := by
  refine ⟨h.1, ?_⟩
  apply prefix_cursor_guarded (op := .SLOAD) (arg := none) h.2
    (by simp only [h.1, hdec, Option.getD_some]) (by decide)
    (fun s => s.machineState.gasAvailable.toNat < Csload (a :: t) s.substate s.executionEnv) (fun s => stSload s a t)
  · intro s matched
    rw [h.1]
    exact sload_xstep ((congrArg ExecutionEnv.code matched.1).trans h.1) matched.2.1 hdec matched.2.2.1 hov
  · intro s matched
    rcases matched with ⟨hee, hpc, hstk, hmem, haw, hrdata, hworld⟩
    have hcA := congrArg Prod.fst hworld
    have hσ := congrArg Prod.snd hworld
    dsimp only at hcA hσ
    simp only [and_self, CursorMatches, stSload, hee, hpc, hmem, haw, hrdata, hcA, hσ]

theorem PCR.sstore {code : ByteArray} {ee : ExecutionEnv} {target child : Ethereum.State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {slot val : UInt256} {t : List UInt256}
    (h : PCR code ee target child pc (slot :: val :: t) mem aw rdata (cA, σ))
    (hperm : ee.perm = true)
    (hdec : decode code pc = some (.SSTORE, .none))
    (hov : t.length ≤ 1024) :
    PCR code ee target child (pc + ⟨1⟩) t mem aw rdata
      (cA, sstoreAccountMap ee.codeOwner σ slot val) := by
  refine ⟨h.1, ?_⟩
  apply prefix_cursor_guarded (op := .SSTORE) (arg := none) h.2
    (by simp only [h.1, hdec, Option.getD_some]) (by decide)
    (fun s => s.machineState.gasAvailable.toNat < max (Csstore s) (GasConstants.Gcallstipend + 1)) (fun s => stSStore s slot val t)
  · intro s matched
    rw [h.1]
    exact sstore_xstep ((congrArg ExecutionEnv.code matched.1).trans h.1) matched.2.1 hdec (by rw [matched.1]; exact hperm) matched.2.2.1 hov
  · intro s matched
    rcases matched with ⟨hee, hpc, hstk, hmem, haw, hrdata, hworld⟩
    have hcA := congrArg Prod.fst hworld
    have hσ := congrArg Prod.snd hworld
    dsimp only at hcA hσ
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rwa [stSStore_executionEnv]
    · rw [stSStore_pc, hpc]
    · exact stSStore_stack s slot val t
    · rwa [stSStore_memory]
    · rwa [stSStore_activeWords]
    · exact hrdata
    · rw [stSStore_createdAccounts, stSStore_accountMap, hcA, hσ, hee]

end Rollup.EVM
