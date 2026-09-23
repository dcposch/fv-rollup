import proofs.PrefixReach

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Rollup.EVM

theorem PCR.dup1 {code : ByteArray} {ee : ExecutionEnv} {target child : Ethereum.State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {a : UInt256} {t : List UInt256}
    (h : PCR code ee target child pc (a :: t) mem aw rdata acc)
    (hdec : decode code pc = some (.DUP1, .none)) (hov : t.length + 2 ≤ 1024) :
    PCR code ee target child (pc + ⟨1⟩) (a :: a :: t) mem aw rdata acc := by
  refine ⟨h.1, ?_⟩
  apply prefix_cursor_guarded (op := .DUP1) (arg := none) h.2
    (by simp only [h.1, hdec, Option.getD_some]) (by decide)
    (fun s => s.machineState.gasAvailable.toNat < 3) (fun s => stDup1 s a t)
  · intro s matched
    rw [h.1]
    exact dup1_xstep ((congrArg ExecutionEnv.code matched.1).trans h.1) matched.2.1 hdec matched.2.2.1 hov
  · intro s matched
    rcases matched with ⟨hee, hpc, hstk, hmem, haw, hrdata, hworld⟩
    simp only [and_self, CursorMatches, stDup1, hee, hpc, hmem, haw, hrdata, hworld]

theorem PCR.iszero {code : ByteArray} {ee : ExecutionEnv} {target child : Ethereum.State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {a : UInt256} {t : List UInt256}
    (h : PCR code ee target child pc (a :: t) mem aw rdata acc)
    (hdec : decode code pc = some (.ISZERO, .none)) (hov : t.length + 1 ≤ 1024) :
    PCR code ee target child (pc + ⟨1⟩) (UInt256.isZero a :: t) mem aw rdata acc := by
  refine ⟨h.1, ?_⟩
  apply prefix_cursor_guarded (op := .ISZERO) (arg := none) h.2
    (by simp only [h.1, hdec, Option.getD_some]) (by decide)
    (fun s => s.machineState.gasAvailable.toNat < 3) (fun s => stIsZero s a t)
  · intro s matched
    rw [h.1]
    exact iszero_xstep ((congrArg ExecutionEnv.code matched.1).trans h.1) matched.2.1 hdec matched.2.2.1 hov
  · intro s matched
    rcases matched with ⟨hee, hpc, hstk, hmem, haw, hrdata, hworld⟩
    simp only [and_self, CursorMatches, stIsZero, hee, hpc, hmem, haw, hrdata, hworld]

theorem PCR.pop {code : ByteArray} {ee : ExecutionEnv} {target child : Ethereum.State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {a : UInt256} {t : List UInt256}
    (h : PCR code ee target child pc (a :: t) mem aw rdata acc)
    (hdec : decode code pc = some (.POP, .none))
    (hov : t.length ≤ 1024) :
    PCR code ee target child (pc + ⟨1⟩) t mem aw rdata acc := by
  refine ⟨h.1, ?_⟩
  apply prefix_cursor_guarded (op := .POP) (arg := none) h.2
    (by simp only [h.1, hdec, Option.getD_some]) (by decide)
    (fun s => s.machineState.gasAvailable.toNat < 2) (fun s => stPop s t)
  · intro s matched
    rw [h.1]
    exact pop_xstep ((congrArg ExecutionEnv.code matched.1).trans h.1) matched.2.1 hdec matched.2.2.1 hov
  · intro s matched
    rcases matched with ⟨hee, hpc, hstk, hmem, haw, hrdata, hworld⟩
    simp only [and_self, CursorMatches, stPop, hee, hpc, hmem, haw, hrdata, hworld]

theorem PCR.callvalue {code : ByteArray} {ee : ExecutionEnv} {target child : Ethereum.State}
    {pc : UInt256} {stk : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : PCR code ee target child pc stk mem aw rdata acc)
    (hdec : decode code pc = some (.CALLVALUE, .none))
    (hov : stk.length + 1 ≤ 1024) :
    PCR code ee target child (pc + ⟨1⟩) (ee.weiValue :: stk) mem aw rdata acc := by
  refine ⟨h.1, ?_⟩
  apply prefix_cursor_guarded (op := .CALLVALUE) (arg := none) h.2
    (by simp only [h.1, hdec, Option.getD_some]) (by decide)
    (fun s => s.machineState.gasAvailable.toNat < 2) (fun s => stCallvalue s)
  · intro s matched
    rw [h.1]
    exact callvalue_xstep ((congrArg ExecutionEnv.code matched.1).trans h.1) matched.2.1 hdec matched.2.2.1 hov
  · intro s matched
    rcases matched with ⟨hee, hpc, hstk, hmem, haw, hrdata, hworld⟩
    simp only [and_self, CursorMatches, stCallvalue, hee, hpc, hstk, hmem, haw, hrdata, hworld]

theorem PCR.calldatasize {code : ByteArray} {ee : ExecutionEnv} {target child : Ethereum.State}
    {pc : UInt256} {stk : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : PCR code ee target child pc stk mem aw rdata acc)
    (hdec : decode code pc = some (.CALLDATASIZE, .none))
    (hov : stk.length + 1 ≤ 1024) :
    PCR code ee target child (pc + ⟨1⟩) (UInt256.ofNat ee.calldata.size :: stk) mem aw rdata acc := by
  refine ⟨h.1, ?_⟩
  apply prefix_cursor_guarded (op := .CALLDATASIZE) (arg := none) h.2
    (by simp only [h.1, hdec, Option.getD_some]) (by decide)
    (fun s => s.machineState.gasAvailable.toNat < 2) (fun s => stCalldatasize s)
  · intro s matched
    rw [h.1]
    exact calldatasize_xstep ((congrArg ExecutionEnv.code matched.1).trans h.1) matched.2.1 hdec matched.2.2.1 hov
  · intro s matched
    rcases matched with ⟨hee, hpc, hstk, hmem, haw, hrdata, hworld⟩
    simp only [and_self, CursorMatches, stCalldatasize, hee, hpc, hstk, hmem, haw, hrdata, hworld]

theorem PCR.calldataload {code : ByteArray} {ee : ExecutionEnv} {target child : Ethereum.State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {a : UInt256} {t : List UInt256}
    (h : PCR code ee target child pc (a :: t) mem aw rdata acc)
    (hdec : decode code pc = some (.CALLDATALOAD, .none))
    (hov : t.length + 1 ≤ 1024) :
    PCR code ee target child (pc + ⟨1⟩)
        (uInt256OfByteArray (ee.calldata.readBytes a.toNat 32) :: t) mem aw rdata acc := by
  refine ⟨h.1, ?_⟩
  apply prefix_cursor_guarded (op := .CALLDATALOAD) (arg := none) h.2
    (by simp only [h.1, hdec, Option.getD_some]) (by decide)
    (fun s => s.machineState.gasAvailable.toNat < 3) (fun s => stCalldataload s a t)
  · intro s matched
    rw [h.1]
    exact calldataload_xstep ((congrArg ExecutionEnv.code matched.1).trans h.1) matched.2.1 hdec matched.2.2.1 hov
  · intro s matched
    rcases matched with ⟨hee, hpc, hstk, hmem, haw, hrdata, hworld⟩
    simp only [and_self, CursorMatches, stCalldataload, hee, hpc, hmem, haw, hrdata, hworld]

theorem PCR.jump {code : ByteArray} {ee : ExecutionEnv} {target child : Ethereum.State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {a : UInt256} {t : List UInt256}
    (h : PCR code ee target child pc (a :: t) mem aw rdata acc)
    (hdec : decode code pc = some (.JUMP, .none))
    (hjd : (D_J code 0).contains a = true)
    (hov : t.length ≤ 1024) :
    PCR code ee target child a t mem aw rdata acc := by
  refine ⟨h.1, ?_⟩
  apply prefix_cursor_guarded (op := .JUMP) (arg := none) h.2
    (by simp only [h.1, hdec, Option.getD_some]) (by decide)
    (fun s => s.machineState.gasAvailable.toNat < 8) (fun s => stJump s a t)
  · intro s matched
    rw [h.1]
    exact jump_xstep ((congrArg ExecutionEnv.code matched.1).trans h.1) matched.2.1 hdec matched.2.2.1 hjd hov
  · intro s matched
    rcases matched with ⟨hee, hpc, hstk, hmem, haw, hrdata, hworld⟩
    simp only [and_self, CursorMatches, stJump, hee, hmem, haw, hrdata, hworld]

theorem PCR.jumpiT {code : ByteArray} {ee : ExecutionEnv} {target child : Ethereum.State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {a b : UInt256} {t : List UInt256}
    (h : PCR code ee target child pc (a :: b :: t) mem aw rdata acc)
    (hdec : decode code pc = some (.JUMPI, .none))
    (hb : b ≠ ⟨0⟩)
    (hjd : (D_J code 0).contains a = true)
    (hov : t.length ≤ 1024) :
    PCR code ee target child a t mem aw rdata acc := by
  refine ⟨h.1, ?_⟩
  apply prefix_cursor_guarded (op := .JUMPI) (arg := none) h.2
    (by simp only [h.1, hdec, Option.getD_some]) (by decide)
    (fun s => s.machineState.gasAvailable.toNat < 10) (fun s => stJumpiT s a t)
  · intro s matched
    rw [h.1]
    exact jumpi_t_xstep ((congrArg ExecutionEnv.code matched.1).trans h.1) matched.2.1 hdec matched.2.2.1 hb hjd hov
  · intro s matched
    rcases matched with ⟨hee, hpc, hstk, hmem, haw, hrdata, hworld⟩
    simp only [and_self, CursorMatches, stJumpiT, hee, hmem, haw, hrdata, hworld]

theorem PCR.jumpiNT {code : ByteArray} {ee : ExecutionEnv} {target child : Ethereum.State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {a b : UInt256} {t : List UInt256}
    (h : PCR code ee target child pc (a :: b :: t) mem aw rdata acc)
    (hdec : decode code pc = some (.JUMPI, .none))
    (hb : b = ⟨0⟩)
    (hov : t.length ≤ 1024) :
    PCR code ee target child (pc + ⟨1⟩) t mem aw rdata acc := by
  refine ⟨h.1, ?_⟩
  apply prefix_cursor_guarded (op := .JUMPI) (arg := none) h.2
    (by simp only [h.1, hdec, Option.getD_some]) (by decide)
    (fun s => s.machineState.gasAvailable.toNat < 10) (fun s => stJumpiNT s t)
  · intro s matched
    rw [h.1]
    have items := matched.2.2.1
    rw [hb] at items
    exact jumpi_nt_xstep ((congrArg ExecutionEnv.code matched.1).trans h.1) matched.2.1 hdec items hov
  · intro s matched
    rcases matched with ⟨hee, hpc, hstk, hmem, haw, hrdata, hworld⟩
    simp only [and_self, CursorMatches, stJumpiNT, hee, hpc, hmem, haw, hrdata, hworld]

end Rollup.EVM
