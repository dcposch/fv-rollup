import proofs.PrefixReach

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Rollup.EVM

-- These stack rules use the pinned EquiVM single-instruction lemmas.

theorem PCR.eq {code : ByteArray} {ee : ExecutionEnv} {target child : Ethereum.State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {a b : UInt256} {t : List UInt256}
    (h : PCR code ee target child pc (a :: b :: t) mem aw rdata acc)
    (hdec : decode code pc = some (.EQ, .none)) (hov : t.length + 1 ≤ 1024) :
    PCR code ee target child (pc + ⟨1⟩) (UInt256.eq a b :: t) mem aw rdata acc :=
  h.stepStack hdec (by decide) (fun _ hc hp hs => eq_xstep hc hp hdec hs hov)

theorem PCR.lt {code : ByteArray} {ee : ExecutionEnv} {target child : Ethereum.State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {a b : UInt256} {t : List UInt256}
    (h : PCR code ee target child pc (a :: b :: t) mem aw rdata acc)
    (hdec : decode code pc = some (.LT, .none)) (hov : t.length + 1 ≤ 1024) :
    PCR code ee target child (pc + ⟨1⟩) (UInt256.lt a b :: t) mem aw rdata acc :=
  h.stepStack hdec (by decide) (fun _ hc hp hs => lt_xstep hc hp hdec hs hov)

theorem PCR.gt {code : ByteArray} {ee : ExecutionEnv} {target child : Ethereum.State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {a b : UInt256} {t : List UInt256}
    (h : PCR code ee target child pc (a :: b :: t) mem aw rdata acc)
    (hdec : decode code pc = some (.GT, .none)) (hov : t.length + 1 ≤ 1024) :
    PCR code ee target child (pc + ⟨1⟩) (UInt256.gt a b :: t) mem aw rdata acc :=
  h.stepStack hdec (by decide) (fun _ hc hp hs => gt_xstep hc hp hdec hs hov)

theorem PCR.slt {code : ByteArray} {ee : ExecutionEnv} {target child : Ethereum.State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {a b : UInt256} {t : List UInt256}
    (h : PCR code ee target child pc (a :: b :: t) mem aw rdata acc)
    (hdec : decode code pc = some (.SLT, .none)) (hov : t.length + 1 ≤ 1024) :
    PCR code ee target child (pc + ⟨1⟩) (UInt256.slt a b :: t) mem aw rdata acc :=
  h.stepStack hdec (by decide) (fun _ hc hp hs => slt_xstep hc hp hdec hs hov)

theorem PCR.shr {code : ByteArray} {ee : ExecutionEnv} {target child : Ethereum.State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {a b : UInt256} {t : List UInt256}
    (h : PCR code ee target child pc (a :: b :: t) mem aw rdata acc)
    (hdec : decode code pc = some (.SHR, .none)) (hov : t.length + 1 ≤ 1024) :
    PCR code ee target child (pc + ⟨1⟩) (UInt256.shiftRight b a :: t) mem aw rdata acc :=
  h.stepStack hdec (by decide) (fun _ hc hp hs => shr_xstep hc hp hdec hs hov)

theorem PCR.sub {code : ByteArray} {ee : ExecutionEnv} {target child : Ethereum.State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {a b : UInt256} {t : List UInt256}
    (h : PCR code ee target child pc (a :: b :: t) mem aw rdata acc)
    (hdec : decode code pc = some (.SUB, .none)) (hov : t.length + 1 ≤ 1024) :
    PCR code ee target child (pc + ⟨1⟩) (UInt256.sub a b :: t) mem aw rdata acc :=
  h.stepStack hdec (by decide) (fun _ hc hp hs => sub_xstep hc hp hdec hs hov)

theorem PCR.and {code : ByteArray} {ee : ExecutionEnv} {target child : Ethereum.State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {a b : UInt256} {t : List UInt256}
    (h : PCR code ee target child pc (a :: b :: t) mem aw rdata acc)
    (hdec : decode code pc = some (.AND, .none)) (hov : t.length + 1 ≤ 1024) :
    PCR code ee target child (pc + ⟨1⟩) (UInt256.land a b :: t) mem aw rdata acc :=
  h.stepStack hdec (by decide) (fun _ hc hp hs => and_xstep hc hp hdec hs hov)

theorem PCR.add {code : ByteArray} {ee : ExecutionEnv} {target child : Ethereum.State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {a b : UInt256} {t : List UInt256}
    (h : PCR code ee target child pc (a :: b :: t) mem aw rdata acc)
    (hdec : decode code pc = some (.ADD, .none)) (hov : t.length + 1 ≤ 1024) :
    PCR code ee target child (pc + ⟨1⟩) ((a + b) :: t) mem aw rdata acc :=
  h.stepStack hdec (by decide) (fun _ hc hp hs => add_xstep hc hp hdec hs hov)

theorem PCR.shl {code : ByteArray} {ee : ExecutionEnv} {target child : Ethereum.State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {a b : UInt256} {t : List UInt256}
    (h : PCR code ee target child pc (a :: b :: t) mem aw rdata acc)
    (hdec : decode code pc = some (.SHL, .none)) (hov : t.length + 1 ≤ 1024) :
    PCR code ee target child (pc + ⟨1⟩) (UInt256.shiftLeft b a :: t) mem aw rdata acc :=
  h.stepStack hdec (by decide) (fun _ hc hp hs => shl_xstep hc hp hdec hs hov)

theorem PCR.swap1 {code : ByteArray} {ee : ExecutionEnv} {target child : Ethereum.State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {a b : UInt256} {t : List UInt256}
    (h : PCR code ee target child pc (a :: b :: t) mem aw rdata acc)
    (hdec : decode code pc = some (.SWAP1, .none)) (hov : t.length + 2 ≤ 1024) :
    PCR code ee target child (pc + ⟨1⟩) (b :: a :: t) mem aw rdata acc :=
  h.stepStack hdec (by decide) (fun _ hc hp hs => swap1_xstep hc hp hdec hs hov)

theorem PCR.swap2 {code : ByteArray} {ee : ExecutionEnv} {target child : Ethereum.State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {a b c : UInt256} {t : List UInt256}
    (h : PCR code ee target child pc (a :: b :: c :: t) mem aw rdata acc)
    (hdec : decode code pc = some (.SWAP2, .none)) (hov : t.length + 3 ≤ 1024) :
    PCR code ee target child (pc + ⟨1⟩) (c :: b :: a :: t) mem aw rdata acc :=
  h.stepStack hdec (by decide) (fun _ hc hp hs => swap2_xstep hc hp hdec hs hov)

theorem PCR.swap3 {code : ByteArray} {ee : ExecutionEnv} {target child : Ethereum.State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {a b c d : UInt256} {t : List UInt256}
    (h : PCR code ee target child pc (a :: b :: c :: d :: t) mem aw rdata acc)
    (hdec : decode code pc = some (.SWAP3, .none)) (hov : t.length + 4 ≤ 1024) :
    PCR code ee target child (pc + ⟨1⟩) (d :: b :: c :: a :: t) mem aw rdata acc :=
  h.stepStack hdec (by decide) (fun _ hc hp hs => swap3_xstep hc hp hdec hs hov)

theorem PCR.swap4 {code : ByteArray} {ee : ExecutionEnv} {target child : Ethereum.State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {a b c d e : UInt256} {t : List UInt256}
    (h : PCR code ee target child pc (a :: b :: c :: d :: e :: t) mem aw rdata acc)
    (hdec : decode code pc = some (.SWAP4, .none)) (hov : t.length + 5 ≤ 1024) :
    PCR code ee target child (pc + ⟨1⟩) (e :: b :: c :: d :: a :: t) mem aw rdata acc :=
  h.stepStack hdec (by decide) (fun _ hc hp hs => swap4_xstep hc hp hdec hs hov)

theorem PCR.swap5 {code : ByteArray} {ee : ExecutionEnv} {target child : Ethereum.State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {a b c d e f : UInt256} {t : List UInt256}
    (rd : PCR code ee target child pc (a :: b :: c :: d :: e :: f :: t) mem aw rdata acc)
    (hdec : decode code pc = some (.SWAP5, .none)) (hov : t.length + 6 ≤ 1024) :
    PCR code ee target child (pc + ⟨1⟩) (f :: b :: c :: d :: e :: a :: t) mem aw rdata acc :=
  rd.stepStack hdec (by decide) (fun _ hc hp hs => swap5_xstep hc hp hdec hs hov)

theorem PCR.swap6 {code : ByteArray} {ee : ExecutionEnv} {target child : Ethereum.State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {a b c d e f gg : UInt256} {t : List UInt256}
    (rd : PCR code ee target child pc (a :: b :: c :: d :: e :: f :: gg :: t) mem aw rdata acc)
    (hdec : decode code pc = some (.SWAP6, .none)) (hov : t.length + 7 ≤ 1024) :
    PCR code ee target child (pc + ⟨1⟩) (gg :: b :: c :: d :: e :: f :: a :: t) mem aw rdata acc :=
  rd.stepStack hdec (by decide) (fun _ hc hp hs => swap6_xstep hc hp hdec hs hov)

theorem PCR.swap7 {code : ByteArray} {ee : ExecutionEnv} {target child : Ethereum.State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {a b c d e f gg h : UInt256} {t : List UInt256}
    (rd : PCR code ee target child pc (a :: b :: c :: d :: e :: f :: gg :: h :: t)
      mem aw rdata acc)
    (hdec : decode code pc = some (.SWAP7, .none)) (hov : t.length + 8 ≤ 1024) :
    PCR code ee target child (pc + ⟨1⟩) (h :: b :: c :: d :: e :: f :: gg :: a :: t)
      mem aw rdata acc :=
  rd.stepStack hdec (by decide) (fun _ hc hp hs => swap7_xstep hc hp hdec hs hov)

theorem PCR.swap8 {code : ByteArray} {ee : ExecutionEnv} {target child : Ethereum.State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {a b c d e f gg hh ii : UInt256} {t : List UInt256}
    (rd : PCR code ee target child pc (a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: t)
      mem aw rdata acc)
    (hdec : decode code pc = some (.SWAP8, .none)) (hov : t.length + 9 ≤ 1024) :
    PCR code ee target child (pc + ⟨1⟩) (ii :: b :: c :: d :: e :: f :: gg :: hh :: a :: t)
      mem aw rdata acc :=
  rd.stepStack hdec (by decide) (fun _ hc hp hs => swap8_xstep hc hp hdec hs hov)

theorem PCR.dup2 {code : ByteArray} {ee : ExecutionEnv} {target child : Ethereum.State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {a b : UInt256} {t : List UInt256}
    (h : PCR code ee target child pc (a :: b :: t) mem aw rdata acc)
    (hdec : decode code pc = some (.DUP2, .none)) (hov : t.length + 3 ≤ 1024) :
    PCR code ee target child (pc + ⟨1⟩) (b :: a :: b :: t) mem aw rdata acc :=
  h.stepStack hdec (by decide) (fun _ hc hp hs => dup2_xstep hc hp hdec hs hov)

theorem PCR.dup3 {code : ByteArray} {ee : ExecutionEnv} {target child : Ethereum.State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {a b c : UInt256} {t : List UInt256}
    (h : PCR code ee target child pc (a :: b :: c :: t) mem aw rdata acc)
    (hdec : decode code pc = some (.DUP3, .none)) (hov : t.length + 4 ≤ 1024) :
    PCR code ee target child (pc + ⟨1⟩) (c :: a :: b :: c :: t) mem aw rdata acc :=
  h.stepStack hdec (by decide) (fun _ hc hp hs => dup3_xstep hc hp hdec hs hov)

theorem PCR.dup4 {code : ByteArray} {ee : ExecutionEnv} {target child : Ethereum.State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {a b c d : UInt256} {t : List UInt256}
    (h : PCR code ee target child pc (a :: b :: c :: d :: t) mem aw rdata acc)
    (hdec : decode code pc = some (.DUP4, .none)) (hov : t.length + 5 ≤ 1024) :
    PCR code ee target child (pc + ⟨1⟩) (d :: a :: b :: c :: d :: t) mem aw rdata acc :=
  h.stepStack hdec (by decide) (fun _ hc hp hs => dup4_xstep hc hp hdec hs hov)

theorem PCR.dup5 {code : ByteArray} {ee : ExecutionEnv} {target child : Ethereum.State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {a b c d e : UInt256} {t : List UInt256}
    (h : PCR code ee target child pc (a :: b :: c :: d :: e :: t) mem aw rdata acc)
    (hdec : decode code pc = some (.DUP5, .none)) (hov : t.length + 6 ≤ 1024) :
    PCR code ee target child (pc + ⟨1⟩) (e :: a :: b :: c :: d :: e :: t) mem aw rdata acc :=
  h.stepStack hdec (by decide) (fun _ hc hp hs => dup5_xstep hc hp hdec hs hov)

theorem PCR.dup6 {code : ByteArray} {ee : ExecutionEnv} {target child : Ethereum.State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {a b c d e f : UInt256} {t : List UInt256}
    (h : PCR code ee target child pc (a :: b :: c :: d :: e :: f :: t) mem aw rdata acc)
    (hdec : decode code pc = some (.DUP6, .none)) (hov : t.length + 7 ≤ 1024) :
    PCR code ee target child (pc + ⟨1⟩) (f :: a :: b :: c :: d :: e :: f :: t) mem aw rdata acc :=
  h.stepStack hdec (by decide) (fun _ hc hp hs => dup6_xstep hc hp hdec hs hov)

theorem PCR.dup7 {code : ByteArray} {ee : ExecutionEnv} {target child : Ethereum.State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {a b c d e f gg : UInt256} {t : List UInt256}
    (h : PCR code ee target child pc (a :: b :: c :: d :: e :: f :: gg :: t) mem aw rdata acc)
    (hdec : decode code pc = some (.DUP7, .none)) (hov : t.length + 8 ≤ 1024) :
    PCR code ee target child (pc + ⟨1⟩) (gg :: a :: b :: c :: d :: e :: f :: gg :: t) mem aw rdata acc :=
  h.stepStack hdec (by decide) (fun _ hc hp hs => dup7_xstep hc hp hdec hs hov)

theorem PCR.dup8 {code : ByteArray} {ee : ExecutionEnv} {target child : Ethereum.State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {a b c d e f gg hh : UInt256} {t : List UInt256}
    (h : PCR code ee target child pc (a :: b :: c :: d :: e :: f :: gg :: hh :: t) mem aw rdata acc)
    (hdec : decode code pc = some (.DUP8, .none)) (hov : t.length + 9 ≤ 1024) :
    PCR code ee target child (pc + ⟨1⟩) (hh :: a :: b :: c :: d :: e :: f :: gg :: hh :: t) mem aw rdata acc :=
  h.stepStack hdec (by decide) (fun _ hc hp hs => dup8_xstep hc hp hdec hs hov)

end Rollup.EVM
