import proofs.CreationBytecode
import proofs.PackedAddress

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Rollup.EVM

macro "creation_decode_step" : tactic =>
  `(tactic| (rw [creation_decode _ _ (by decide)]; decide))

open Lean in
macro "creation_run " base:term " with " "[" steps:evmStep,* "]" : term => do
  let mut acc := base
  for step in steps.getElems do
    match step with
    | `(evmStep| raw $op:ident $args*) => acc ← `($(acc).$op $args*)
    | `(evmStep| $op:ident $args*) =>
      match op.getId with
      | `jump => acc ← `($(acc).jump (by creation_decode_step) $(args[0]!) (by evm_ov))
      | `jumpiT => acc ← `($(acc).jumpiT (by creation_decode_step) $(args[0]!) $(args[1]!)
          (by evm_ov))
      | `jumpiNT => acc ← `($(acc).jumpiNT (by creation_decode_step) $(args[0]!) (by evm_ov))
      | _ => acc ← `($(acc).$op $args* (by creation_decode_step) (by evm_ov))
    | _ => Macro.throwUnsupported
  return acc

/-- The constructor body rejects the zero sequencer. -/
theorem creation_zero_sequencer {I : ExecutionEnv} {g : Sat256} {s0 : Ethereum.State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (args mem : ByteArray) (root : UInt256)
    (reached : RD (creationBytecode ++ args) I g s0 ⟨43⟩ [root, ⟨0⟩] mem
      (UInt256.ofNat 6) ByteArray.empty acc k C) :
    RDrev (creationBytecode ++ args) g s0 := by
  have beforeGuard := creation_run reached with [
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup3, and, push1 ⟨60⟩]
  have rejected := creation_run beforeGuard with [jumpiNT (by decide), push0, dup1]
  exact rejected.rev 0 (by creation_decode_step)
    (fun s _ stack => memExpRevert0 s stack) (by evm_ov)

/-- The constructor body stores the decoded sequencer and root, then returns code. -/
theorem creation_body_packed {I : ExecutionEnv} {g : Sat256} {s0 : Ethereum.State}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : Nat}
    (args mem : ByteArray) (sequencer root : UInt256)
    (canonical : sequencer.toNat < _root_.EVM.addressModulus)
    (nonzero : sequencer ≠ ⟨0⟩) (writable : I.perm = true)
    (reached : RD (creationBytecode ++ args) I g s0 ⟨43⟩ [root, sequencer] mem
      (UInt256.ofNat 6) ByteArray.empty (cA, σ) k C) :
    RDret (creationBytecode ++ args) g s0
      (cA, sstoreAccountMap I.codeOwner (sstoreAccountMap I.codeOwner σ ⟨0⟩
        (packedAddress (σ.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD ⟨0⟩ ⟨0⟩)) sequencer)) ⟨1⟩ root)
      runtimeBytecode := by
  have mask : UInt256.sub (UInt256.shiftLeft ⟨1⟩ ⟨160⟩) ⟨1⟩ = solcAddrMask := by decide
  have clean := solcAddrMask_clean canonical
  have beforeGuard := creation_run reached with [
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup3, and, push1 ⟨60⟩]
  have guard := beforeGuard.jumpiT (by creation_decode_step)
    (by simpa only [mask, clean] using nonzero)
    (D_J_contains_append_left _ args _ (jumpScan_valid creationBytecode 60 100 (by decide)))
    (by evm_ov)
  have beforeLoad := creation_run guard with [jumpdest, push0, dup1]
  obtain ⟨_, _, loaded⟩ := beforeLoad.sload (by creation_decode_step) (by evm_ov)
  have beforeStore := creation_run loaded with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, not, and,
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub,
    swap4, swap1, swap4, and, swap3, swap1, swap3, or, swap1, swap2]
  simp only [mask] at beforeStore
  rw [← packedAddress] at beforeStore
  obtain ⟨_, _, storedSequencer⟩ := beforeStore.sstore writable
    (by creation_decode_step) (by evm_ov)
  have rootSlot := creation_run storedSequencer with [push1 ⟨1⟩]
  obtain ⟨_, _, storedRoot⟩ := rootSlot.sstore writable (by creation_decode_step) (by evm_ov)
  have returning := creation_run storedRoot with [push1 ⟨152⟩,
    jump (D_J_contains_append_left _ args _ (jumpScan_valid creationBytecode 152 160 (by decide)))]
  exact creation_return args mem returning

/-- A fresh sequencer slot contains only the new address. -/
theorem creation_body {I : ExecutionEnv} {g : Sat256} {s0 : Ethereum.State}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : Nat}
    (args mem : ByteArray) (sequencer root : UInt256)
    (canonical : sequencer.toNat < _root_.EVM.addressModulus)
    (nonzero : sequencer ≠ ⟨0⟩) (writable : I.perm = true)
    (fresh : (σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨0⟩ ⟨0⟩)) = ⟨0⟩)
    (reached : RD (creationBytecode ++ args) I g s0 ⟨43⟩ [root, sequencer] mem
      (UInt256.ofNat 6) ByteArray.empty (cA, σ) k C) :
    RDret (creationBytecode ++ args) g s0
      (cA, sstoreAccountMap I.codeOwner (sstoreAccountMap I.codeOwner σ ⟨0⟩ sequencer) ⟨1⟩ root)
      runtimeBytecode := by
  simpa only [fresh, packedAddress_zero sequencer canonical] using
    creation_body_packed args mem sequencer root canonical nonzero writable reached

end Rollup.EVM
