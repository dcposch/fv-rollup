import proofs.PrefixReach

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Rollup.EVM

/-- The GAS word comes from the actual instruction state. -/
theorem PCR.gas {code : ByteArray} {ee : ExecutionEnv} {target child : Ethereum.State}
    {pc : UInt256} {stack : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (reached : PCR code ee target child pc stack mem aw rdata acc)
    (decoded : decode code pc = some (.GAS, none)) (space : stack.length + 1 ≤ 1024) :
    ∃ value, PCR code ee target child (pc + ⟨1⟩) (value :: stack) mem aw rdata acc := by
  have next := prefix_cursor_step_exists
    (op := .GAS) (arg := none)
    (fun value : UInt256 => ⟨pc + ⟨1⟩, value :: stack, mem, aw, rdata, acc⟩)
    reached.2 (by simp only [reached.1, decoded, Option.getD_some]) (by decide)
  obtain ⟨value, carried⟩ := next (by
    intro before after matched run
    have step := gas_xstep ((congrArg ExecutionEnv.code matched.1).trans reached.1)
      matched.2.1 decoded matched.2.2.1 space
    rw [reached.1, step] at run
    split at run <;> try contradiction
    have same := congrArg Prod.fst (Except.ok.inj run)
    dsimp only at same
    subst after
    refine ⟨(before.machineState.gasAvailable.subNat 2).toUInt256, ?_⟩
    apply cursor_matches_restore_depth matched.1
    rcases matched with ⟨hee, hpc, hstk, hmem, haw, hrdata, hworld⟩
    simp only [and_self, CursorMatches, stGas, hee, hpc, hstk, hmem, haw, hrdata, hworld])
  exact ⟨value, reached.1, carried⟩

end Rollup.EVM
