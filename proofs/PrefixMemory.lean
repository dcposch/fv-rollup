import proofs.PrefixReach

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Rollup.EVM

theorem PCR.mstore {code : ByteArray} {ee : ExecutionEnv} {target child : Ethereum.State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {a b : UInt256} {t : List UInt256} (mcost : ℕ) (memout : ByteArray) (awout : UInt256)
    (h : PCR code ee target child pc (a :: b :: t) mem aw rdata acc)
    (hdec : decode code pc = some (.MSTORE, .none))
    (hmc : ∀ s : Ethereum.State, s.machineState.activeWords = aw → s.machineState.stack = a :: b :: t →
        memoryExpansionCost s .MSTORE = mcost)
    (hmemout : b.toByteArray.write 0 mem a.toNat 32 = memout)
    (hawout : UInt256.ofNat (MachineState.M aw.toNat a.toNat 32) = awout)
    (hov : t.length ≤ 1024) :
    PCR code ee target child (pc + ⟨1⟩) t memout awout rdata acc := by
  refine ⟨h.1, ?_⟩
  apply prefix_cursor_guarded (op := .MSTORE) (arg := none) h.2
    (by simp only [h.1, hdec, Option.getD_some]) (by decide)
    (fun s => s.machineState.gasAvailable.toNat < mcost + 3) (fun s => stMStore s a b t)
  · intro s matched
    rw [h.1]
    have step := mstore_xstep ((congrArg ExecutionEnv.code matched.1).trans h.1) matched.2.1 hdec matched.2.2.1 hov
    rw [hmc s matched.2.2.2.2.1 matched.2.2.1] at step
    exact step
  · intro s matched
    rcases matched with ⟨hee, hpc, hstk, hmem, haw, hrdata, hworld⟩
    simp only [and_self, CursorMatches, stMStore, hee, hpc, hmem, haw, hrdata, hworld, hmemout, hawout]

theorem PCR.mload {code : ByteArray} {ee : ExecutionEnv} {target child : Ethereum.State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {a : UInt256} {t : List UInt256} (mcost : ℕ) (loadval awout : UInt256)
    (h : PCR code ee target child pc (a :: t) mem aw rdata acc)
    (hdec : decode code pc = some (.MLOAD, .none))
    (hmc : ∀ s : Ethereum.State, s.machineState.activeWords = aw → s.machineState.stack = a :: t →
        memoryExpansionCost s .MLOAD = mcost)
    (hval : (if a.toNat ≥ mem.size ∨ a ≥ aw * ⟨32⟩ then ⟨0⟩
             else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding a.toNat 32))) = loadval)
    (hawout : UInt256.ofNat (MachineState.M aw.toNat a.toNat 32) = awout)
    (hov : t.length + 1 ≤ 1024) :
    PCR code ee target child (pc + ⟨1⟩) (loadval :: t) mem awout rdata acc := by
  refine ⟨h.1, ?_⟩
  apply prefix_cursor_guarded (op := .MLOAD) (arg := none) h.2
    (by simp only [h.1, hdec, Option.getD_some]) (by decide)
    (fun s => s.machineState.gasAvailable.toNat < mcost + 3) (fun s => stMLoad s a t)
  · intro s matched
    rw [h.1]
    have step := mload_xstep ((congrArg ExecutionEnv.code matched.1).trans h.1) matched.2.1 hdec matched.2.2.1 hov
    rw [hmc s matched.2.2.2.2.1 matched.2.2.1] at step
    exact step
  · intro s matched
    rcases matched with ⟨hee, hpc, hstk, hmem, haw, hrdata, hworld⟩
    simp only [and_self, CursorMatches, stMLoad, hee, hpc, hmem, haw, hrdata, hworld, hval, hawout]

theorem PCR.keccak256 {code : ByteArray} {ee : ExecutionEnv} {target child : Ethereum.State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {a b : UInt256} {t : List UInt256} (mcost : ℕ) (kecval awout : UInt256)
    (h : PCR code ee target child pc (a :: b :: t) mem aw rdata acc)
    (hdec : decode code pc = some (.KECCAK256, .none))
    (hmc : ∀ s : Ethereum.State, s.machineState.activeWords = aw → s.machineState.stack = a :: b :: t →
        memoryExpansionCost s .KECCAK256 = mcost)
    (hval : UInt256.ofNat (fromByteArrayBigEndian
              (ffi.KEC (mem.readWithPadding a.toNat b.toNat))) = kecval)
    (hawout : UInt256.ofNat (MachineState.M aw.toNat a.toNat b.toNat) = awout)
    (hov : t.length + 1 ≤ 1024) :
    PCR code ee target child (pc + ⟨1⟩) (kecval :: t) mem awout rdata acc := by
  refine ⟨h.1, ?_⟩
  apply prefix_cursor_guarded (op := .KECCAK256) (arg := none) h.2
    (by simp only [h.1, hdec, Option.getD_some]) (by decide)
    (fun s => s.machineState.gasAvailable.toNat < mcost + (GasConstants.Gkeccak256 + GasConstants.Gkeccak256word * ((b.toNat + 31) / 32))) (fun s => stKeccak s a b t)
  · intro s matched
    rw [h.1]
    have step := keccak_xstep ((congrArg ExecutionEnv.code matched.1).trans h.1) matched.2.1 hdec matched.2.2.1 hov
    rw [hmc s matched.2.2.2.2.1 matched.2.2.1] at step
    exact step
  · intro s matched
    rcases matched with ⟨hee, hpc, hstk, hmem, haw, hrdata, hworld⟩
    simp only [and_self, CursorMatches, stKeccak, hee, hpc, hmem, haw, hrdata, hworld, hval, hawout]

end Rollup.EVM
