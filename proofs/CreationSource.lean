import proofs.Constructor

open Solm Ethereum Reasoning.Theory

namespace Rollup.EVM

def constructorABIStore (sequencer : Address) (root : Root) : Store :=
  Std.HashMap.ofList [("sequencer_", .address sequencer), ("initialRoot", rootValue root)]

theorem constructorABIStore_seq (sequencer : Address) (root : Root) :
    (constructorABIStore sequencer root).get? "sequencer_" = some (.address sequencer) := by
  apply Std.HashMap.getElem?_ofList_of_mem (k := "sequencer_") (by decide)
    (by simp) (by simp)

theorem constructorABIStore_root (sequencer : Address) (root : Root) :
    (constructorABIStore sequencer root).get? "initialRoot" = some (rootValue root) := by
  apply Std.HashMap.getElem?_ofList_of_mem (k := "initialRoot") (by decide)
    (by simp) (by simp)

theorem constructorABIStore_noSeq (sequencer : Address) (root : Root) :
    (constructorABIStore sequencer root).get? "sequencer" = none :=
  Std.HashMap.getElem?_ofList_of_contains_eq_false (by simp)

theorem constructorABIStore_noRoot (sequencer : Address) (root : Root) :
    (constructorABIStore sequencer root).get? "stateRoot" = none :=
  Std.HashMap.getElem?_ofList_of_contains_eq_false (by simp)

/-- The source constructor executes with the library's ABI parameter store. -/
theorem constructor_solm_success {cA gh bl σ σ₀ A I} {g : UInt256}
    (sequencer : Address) (root : Root) (nonzero : sequencer ≠ 0)
    (value : I.weiValue = ⟨0⟩) :
    solmCtorExec config contract [.address sequencer, rootValue root] cA gh bl σ σ₀ g A I
      (.returned ⟨contract, constructorABIStore sequencer root⟩
        (constructorPackedState (initState cA gh bl σ σ₀ (.ofUInt256 g) A I) sequencer root) none) := by
  refine solmCtorExec.intro (evmState := initState cA gh bl σ σ₀ (.ofUInt256 g) A I)
    (argsStore := constructorABIStore sequencer root) rfl rfl rfl ?_
  exact (exact_function (constructor_source_packed _ sequencer root _
    (constructorABIStore_seq sequencer root) (constructorABIStore_root sequencer root)
    (constructorABIStore_noSeq sequencer root) (constructorABIStore_noRoot sequencer root)
    nonzero value)).1

theorem constructor_solm_nonpayable {cA gh bl σ σ₀ A I} {g : UInt256}
    (sequencer : Address) (root : Root) (value : I.weiValue ≠ ⟨0⟩) :
    solmCtorExec config contract [.address sequencer, rootValue root] cA gh bl σ σ₀ g A I
      .reverted := by
  refine solmCtorExec.intro (evmState := initState cA gh bl σ σ₀ (.ofUInt256 g) A I)
    (argsStore := constructorABIStore sequencer root) rfl rfl rfl ?_
  exact bodyReverts_nonPayable value

theorem constructor_solm_zero {cA gh bl σ σ₀ A I} {g : UInt256}
    (root : Root) (value : I.weiValue = ⟨0⟩) :
    solmCtorExec config contract [.address 0, rootValue root] cA gh bl σ σ₀ g A I
      .reverted := by
  refine solmCtorExec.intro (evmState := initState cA gh bl σ σ₀ (.ofUInt256 g) A I)
    (argsStore := constructorABIStore 0 root) rfl rfl rfl ?_
  apply (exact_function_revert (exact_cons (exact_require_true (evalCallvalueEq_true value))
    (exact_require_false ?_))).1
  rw [constructor_seq_guard_get _ 0 _ (constructorABIStore_seq 0 root)]
  rfl

end Rollup.EVM
