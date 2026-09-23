import proofs.CreationDecode

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Rollup.EVM

/-- The full creation code stores valid arguments and returns the pinned runtime, or exhausts gas. -/
theorem creation_execution_packed {cA gh bl σ σ₀ A I} {g : Sat256}
    (sequencer root : UInt256)
    (canonical : sequencer.toNat < _root_.EVM.addressModulus)
    (nonzero : sequencer ≠ ⟨0⟩) (writable : I.perm = true)
    (value : I.weiValue = ⟨0⟩)
    (code : I.code = creationBytecode ++ creationArgs sequencer root) :
    RDret (creationBytecode ++ creationArgs sequencer root) g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner (sstoreAccountMap I.codeOwner σ ⟨0⟩
        (packedAddress (σ.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD ⟨0⟩ ⟨0⟩)) sequencer)) ⟨1⟩ root)
      runtimeBytecode := by
  obtain ⟨_, _, entered⟩ := creation_zero_value (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) _ code value
  obtain ⟨_, _, decoded⟩ := creation_load_args sequencer root canonical entered
  exact creation_body_packed _ _ sequencer root canonical nonzero writable decoded

/-- The full creation code stores valid arguments and returns the pinned runtime, or exhausts gas. -/
theorem creation_execution {cA gh bl σ σ₀ A I} {g : Sat256}
    (sequencer root : UInt256)
    (canonical : sequencer.toNat < _root_.EVM.addressModulus)
    (nonzero : sequencer ≠ ⟨0⟩) (writable : I.perm = true)
    (value : I.weiValue = ⟨0⟩)
    (fresh : (σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨0⟩ ⟨0⟩)) = ⟨0⟩)
    (code : I.code = creationBytecode ++ creationArgs sequencer root) :
    RDret (creationBytecode ++ creationArgs sequencer root) g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner (sstoreAccountMap I.codeOwner σ ⟨0⟩ sequencer) ⟨1⟩ root)
      runtimeBytecode := by
  obtain ⟨_, _, entered⟩ := creation_zero_value (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) _ code value
  obtain ⟨_, _, decoded⟩ := creation_load_args sequencer root canonical entered
  exact creation_body _ _ sequencer root canonical nonzero writable fresh decoded

/-- The full creation code rejects a zero sequencer, or exhausts gas. -/
theorem creation_execution_zero {cA gh bl σ σ₀ A I} {g : Sat256}
    (root : UInt256) (value : I.weiValue = ⟨0⟩)
    (code : I.code = creationBytecode ++ creationArgs ⟨0⟩ root) :
    RDrev (creationBytecode ++ creationArgs ⟨0⟩ root) g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, entered⟩ := creation_zero_value (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) _ code value
  obtain ⟨_, _, decoded⟩ := creation_load_args ⟨0⟩ root (by decide) entered
  exact creation_zero_sequencer _ _ root decoded

/-- The EVM result has the two specified writes and exact runtime bytes, or is out of gas. -/
theorem creation_xi_packed {cA gh bl σ σ₀ A I} {g : UInt256}
    (sequencer root : UInt256)
    (canonical : sequencer.toNat < _root_.EVM.addressModulus)
    (nonzero : sequencer ≠ ⟨0⟩) (writable : I.perm = true)
    (value : I.weiValue = ⟨0⟩)
    (code : I.code = creationBytecode ++ creationArgs sequencer root) :
    Ξ cA gh bl σ σ₀ g A I = .error .OutOfGass ∨
      ∃ gas substate, Ξ cA gh bl σ σ₀ g A I = .ok (.success
        (cA, sstoreAccountMap I.codeOwner (sstoreAccountMap I.codeOwner σ ⟨0⟩
          (packedAddress (σ.find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD ⟨0⟩ ⟨0⟩)) sequencer))
          ⟨1⟩ root, gas, substate) runtimeBytecode) := by
  have execution := creation_execution_packed (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (g := Sat256.ofUInt256 g) sequencer root canonical nonzero writable value code
  rcases execution with outOfGas | ⟨state, result, accounts⟩
  · left
    apply Xi_error_of_X (g := g)
    rw [← code] at outOfGas
    simpa [Sat256.ofUInt256] using outOfGas
  · right
    have success := Xi_success_of_X (g := g) (by
      rw [← code] at result
      simpa [Sat256.ofUInt256] using result)
    have created := congrArg Prod.fst accounts
    have stored := congrArg Prod.snd accounts
    dsimp only at created stored
    rw [created, stored] at success
    exact ⟨_, _, success⟩

/-- The EVM result has the two specified writes and exact runtime bytes, or is out of gas. -/
theorem creation_xi_result {cA gh bl σ σ₀ A I} {g : UInt256}
    (sequencer root : UInt256)
    (canonical : sequencer.toNat < _root_.EVM.addressModulus)
    (nonzero : sequencer ≠ ⟨0⟩) (writable : I.perm = true)
    (value : I.weiValue = ⟨0⟩)
    (fresh : (σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨0⟩ ⟨0⟩)) = ⟨0⟩)
    (code : I.code = creationBytecode ++ creationArgs sequencer root) :
    Ξ cA gh bl σ σ₀ g A I = .error .OutOfGass ∨
      ∃ gas substate, Ξ cA gh bl σ σ₀ g A I = .ok (.success
        (cA, sstoreAccountMap I.codeOwner (sstoreAccountMap I.codeOwner σ ⟨0⟩ sequencer)
          ⟨1⟩ root, gas, substate) runtimeBytecode) := by
  have execution := creation_execution (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀)
    (A := A) (g := Sat256.ofUInt256 g) sequencer root canonical nonzero writable value fresh code
  rcases execution with outOfGas | ⟨state, result, accounts⟩
  · left
    apply Xi_error_of_X (g := g)
    rw [← code] at outOfGas
    simpa [Sat256.ofUInt256] using outOfGas
  · right
    have success := Xi_success_of_X (g := g) (by
      rw [← code] at result
      simpa [Sat256.ofUInt256] using result)
    have created := congrArg Prod.fst accounts
    have stored := congrArg Prod.snd accounts
    dsimp only at created stored
    rw [created, stored] at success
    exact ⟨_, _, success⟩

end Rollup.EVM
