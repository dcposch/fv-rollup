import proofs.CreationExecution
open Ethereum Ethereum.EVM Reasoning.Theory
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
namespace Rollup.EVM
namespace CreationWitness

private theorem execution_step {vj : Array UInt256} {s next : Ethereum.State} {fuel : Nat}
    {post : Ethereum.State → ByteArray → Prop}
    (step : Xstep vj s = .ok (next, .none))
    (rest : ∃ final output, X fuel vj next = .ok (.success final output) ∧ post final output) :
    ∃ final output, X (fuel + 1) vj s = .ok (.success final output) ∧ post final output := by
  obtain ⟨final, output, result, checked⟩ := rest
  exact ⟨final, output, Xstep_X_X_continue fuel s next vj _ step result, checked⟩

private theorem execution_return {vj : Array UInt256} {s next : Ethereum.State} {fuel : Nat}
    {output : ByteArray} {post : Ethereum.State → ByteArray → Prop}
    (step : Xstep vj s = .ok (next, .some (.success, output)))
    (checked : post next output) :
    ∃ final output, X (fuel + 1) vj s = .ok (.success final output) ∧ post final output :=
  ⟨next, output, Xstep_X_X_halt_success fuel s next vj output step, checked⟩

noncomputable def witnessEnv : ExecutionEnv :=
  { (default : ExecutionEnv) with
    codeOwner := 42
    code := creationBytecode ++ ⟨(Array.replicate 31 0).push 1 ++ (Array.replicate 31 0).push 1⟩, perm := true }
noncomputable def witnessStart : Ethereum.State :=
  initState default default default
    ((default : AccountMap).insert 42 { (default : Account) with nonce := ⟨1⟩ }) default
    (1000000 : Sat256) default witnessEnv

macro "witness_step " step:term : tactic =>
  `(tactic| (
    apply execution_step
    · rw [($step)]
      with_unfolding_all rfl))

/-- This constructor run succeeds and leaves enough gas for code deposit. -/
theorem executes : ∃ final output, X 1000001 (D_J witnessEnv.code 0) witnessStart =
    .ok (.success final output) ∧ 285800 ≤ final.machineState.gasAvailable.toNat := by
  witness_step (push1_xstep (code := witnessEnv.code) (pcv := ⟨0⟩) (argv := ⟨128⟩) (rest := []) rfl rfl (by decide) (by with_unfolding_all rfl) (by decide))
  witness_step (push1_xstep (code := witnessEnv.code) (pcv := ⟨2⟩) (argv := ⟨64⟩) (rest := [⟨128⟩]) rfl rfl (by decide) (by with_unfolding_all rfl) (by decide))
  witness_step (mstore_xstep (code := witnessEnv.code) (pcv := ⟨4⟩) (a := ⟨64⟩) (b := ⟨128⟩) (t := []) rfl rfl (by decide) (by with_unfolding_all rfl) (by decide))
  witness_step (callvalue_xstep (code := witnessEnv.code) (pcv := ⟨5⟩) (rest := []) rfl rfl (by decide) (by with_unfolding_all rfl) (by decide))
  witness_step (dup1_xstep (code := witnessEnv.code) (pcv := ⟨6⟩) (a := ⟨0⟩) (t := []) rfl rfl (by decide) (by with_unfolding_all rfl) (by decide))
  witness_step (iszero_xstep (code := witnessEnv.code) (pcv := ⟨7⟩) (a := ⟨0⟩) (t := [⟨0⟩]) rfl rfl (by decide) (by with_unfolding_all rfl) (by decide))
  witness_step (push1_xstep (code := witnessEnv.code) (pcv := ⟨8⟩) (argv := ⟨14⟩) (rest := [⟨1⟩, ⟨0⟩]) rfl rfl (by decide) (by with_unfolding_all rfl) (by decide))
  witness_step (jumpi_t_xstep (code := witnessEnv.code) (pcv := ⟨10⟩) (a := ⟨14⟩) (b := ⟨1⟩) (t := [⟨0⟩]) rfl rfl (by decide) (by with_unfolding_all rfl) (by decide +kernel) (jumpScan_valid witnessEnv.code 14 170 (by decide)) (by decide))
  witness_step (jumpdest_xstep (code := witnessEnv.code) (pcv := ⟨14⟩)  rfl rfl (by decide) (by decide))
  witness_step (pop_xstep (code := witnessEnv.code) (pcv := ⟨15⟩) (a := ⟨0⟩) (t := []) rfl rfl (by decide) (by with_unfolding_all rfl) (by decide))
  witness_step (push1_xstep (code := witnessEnv.code) (pcv := ⟨16⟩) (argv := ⟨64⟩) (rest := []) rfl rfl (by decide) (by with_unfolding_all rfl) (by decide))
  witness_step (mload_xstep (code := witnessEnv.code) (pcv := ⟨18⟩) (a := ⟨64⟩) (t := []) rfl rfl (by decide) (by with_unfolding_all rfl) (by decide))
  witness_step (push2_xstep (code := witnessEnv.code) (pcv := ⟨19⟩) (argv := ⟨1594⟩) (rest := [⟨128⟩]) rfl rfl (by decide) (by with_unfolding_all rfl) (by decide))
  witness_step (codesize_xstep (code := witnessEnv.code) (pcv := ⟨22⟩) (rest := [⟨1594⟩, ⟨128⟩]) rfl rfl (by decide) (by with_unfolding_all rfl) (by decide))
  witness_step (sub_xstep (code := witnessEnv.code) (pcv := ⟨23⟩) (a := ⟨1658⟩) (b := ⟨1594⟩) (t := [⟨128⟩]) rfl rfl (by decide) (by with_unfolding_all rfl) (by decide))
  witness_step (dup1_xstep (code := witnessEnv.code) (pcv := ⟨24⟩) (a := ⟨64⟩) (t := [⟨128⟩]) rfl rfl (by decide) (by with_unfolding_all rfl) (by decide))
  witness_step (push2_xstep (code := witnessEnv.code) (pcv := ⟨25⟩) (argv := ⟨1594⟩) (rest := [⟨64⟩, ⟨64⟩, ⟨128⟩]) rfl rfl (by decide) (by with_unfolding_all rfl) (by decide))
  witness_step (dup4_xstep (code := witnessEnv.code) (pcv := ⟨28⟩) (a := ⟨1594⟩) (b := ⟨64⟩) (c := ⟨64⟩) (d := ⟨128⟩) (t := []) rfl rfl (by decide) (by with_unfolding_all rfl) (by decide))
  witness_step (codecopy_xstep (code := witnessEnv.code) (pcv := ⟨29⟩) (a := ⟨128⟩) (b := ⟨1594⟩) (c := ⟨64⟩) (t := [⟨64⟩, ⟨128⟩]) rfl rfl (by decide) (by with_unfolding_all rfl) (by decide))
  witness_step (dup2_xstep (code := witnessEnv.code) (pcv := ⟨30⟩) (a := ⟨64⟩) (b := ⟨128⟩) (t := []) rfl rfl (by decide) (by with_unfolding_all rfl) (by decide))
  witness_step (add_xstep (code := witnessEnv.code) (pcv := ⟨31⟩) (a := ⟨128⟩) (b := ⟨64⟩) (t := [⟨128⟩]) rfl rfl (by decide) (by with_unfolding_all rfl) (by decide))
  witness_step (push1_xstep (code := witnessEnv.code) (pcv := ⟨32⟩) (argv := ⟨64⟩) (rest := [⟨192⟩, ⟨128⟩]) rfl rfl (by decide) (by with_unfolding_all rfl) (by decide))
  witness_step (dup2_xstep (code := witnessEnv.code) (pcv := ⟨34⟩) (a := ⟨64⟩) (b := ⟨192⟩) (t := [⟨128⟩]) rfl rfl (by decide) (by with_unfolding_all rfl) (by decide))
  witness_step (swap1_xstep (code := witnessEnv.code) (pcv := ⟨35⟩) (a := ⟨192⟩) (b := ⟨64⟩) (t := [⟨192⟩, ⟨128⟩]) rfl rfl (by decide) (by with_unfolding_all rfl) (by decide))
  witness_step (mstore_xstep (code := witnessEnv.code) (pcv := ⟨36⟩) (a := ⟨64⟩) (b := ⟨192⟩) (t := [⟨192⟩, ⟨128⟩]) rfl rfl (by decide) (by with_unfolding_all rfl) (by decide))
  witness_step (push1_xstep (code := witnessEnv.code) (pcv := ⟨37⟩) (argv := ⟨43⟩) (rest := [⟨192⟩, ⟨128⟩]) rfl rfl (by decide) (by with_unfolding_all rfl) (by decide))
  witness_step (swap2_xstep (code := witnessEnv.code) (pcv := ⟨39⟩) (a := ⟨43⟩) (b := ⟨192⟩) (c := ⟨128⟩) (t := []) rfl rfl (by decide) (by with_unfolding_all rfl) (by decide))
  witness_step (push1_xstep (code := witnessEnv.code) (pcv := ⟨40⟩) (argv := ⟨99⟩) (rest := [⟨128⟩, ⟨192⟩, ⟨43⟩]) rfl rfl (by decide) (by with_unfolding_all rfl) (by decide))
  witness_step (jump_xstep (code := witnessEnv.code) (pcv := ⟨42⟩) (a := ⟨99⟩) (t := [⟨128⟩, ⟨192⟩, ⟨43⟩]) rfl rfl (by decide) (by with_unfolding_all rfl) (jumpScan_valid witnessEnv.code 99 170 (by decide)) (by decide))
  witness_step (jumpdest_xstep (code := witnessEnv.code) (pcv := ⟨99⟩)  rfl rfl (by decide) (by decide))
  witness_step (push0_xstep (code := witnessEnv.code) (pcv := ⟨100⟩) (rest := [⟨128⟩, ⟨192⟩, ⟨43⟩]) rfl rfl (by decide) (by with_unfolding_all rfl) (by decide))
  witness_step (dup1_xstep (code := witnessEnv.code) (pcv := ⟨101⟩) (a := ⟨0⟩) (t := [⟨128⟩, ⟨192⟩, ⟨43⟩]) rfl rfl (by decide) (by with_unfolding_all rfl) (by decide))
  witness_step (push1_xstep (code := witnessEnv.code) (pcv := ⟨102⟩) (argv := ⟨64⟩) (rest := [⟨0⟩, ⟨0⟩, ⟨128⟩, ⟨192⟩, ⟨43⟩]) rfl rfl (by decide) (by with_unfolding_all rfl) (by decide))
  witness_step (dup4_xstep (code := witnessEnv.code) (pcv := ⟨104⟩) (a := ⟨64⟩) (b := ⟨0⟩) (c := ⟨0⟩) (d := ⟨128⟩) (t := [⟨192⟩, ⟨43⟩]) rfl rfl (by decide) (by with_unfolding_all rfl) (by decide))
  witness_step (dup6_xstep (code := witnessEnv.code) (pcv := ⟨105⟩) (a := ⟨128⟩) (b := ⟨64⟩) (c := ⟨0⟩) (d := ⟨0⟩) (e := ⟨128⟩) (f := ⟨192⟩) (t := [⟨43⟩]) rfl rfl (by decide) (by with_unfolding_all rfl) (by decide))
  witness_step (sub_xstep (code := witnessEnv.code) (pcv := ⟨106⟩) (a := ⟨192⟩) (b := ⟨128⟩) (t := [⟨64⟩, ⟨0⟩, ⟨0⟩, ⟨128⟩, ⟨192⟩, ⟨43⟩]) rfl rfl (by decide) (by with_unfolding_all rfl) (by decide))
  witness_step (slt_xstep (code := witnessEnv.code) (pcv := ⟨107⟩) (a := ⟨64⟩) (b := ⟨64⟩) (t := [⟨0⟩, ⟨0⟩, ⟨128⟩, ⟨192⟩, ⟨43⟩]) rfl rfl (by decide) (by with_unfolding_all rfl) (by decide))
  witness_step (iszero_xstep (code := witnessEnv.code) (pcv := ⟨108⟩) (a := ⟨0⟩) (t := [⟨0⟩, ⟨0⟩, ⟨128⟩, ⟨192⟩, ⟨43⟩]) rfl rfl (by decide) (by with_unfolding_all rfl) (by decide))
  witness_step (push1_xstep (code := witnessEnv.code) (pcv := ⟨109⟩) (argv := ⟨115⟩) (rest := [⟨1⟩, ⟨0⟩, ⟨0⟩, ⟨128⟩, ⟨192⟩, ⟨43⟩]) rfl rfl (by decide) (by with_unfolding_all rfl) (by decide))
  witness_step (jumpi_t_xstep (code := witnessEnv.code) (pcv := ⟨111⟩) (a := ⟨115⟩) (b := ⟨1⟩) (t := [⟨0⟩, ⟨0⟩, ⟨128⟩, ⟨192⟩, ⟨43⟩]) rfl rfl (by decide) (by with_unfolding_all rfl) (by decide +kernel) (jumpScan_valid witnessEnv.code 115 170 (by decide)) (by decide))
  witness_step (jumpdest_xstep (code := witnessEnv.code) (pcv := ⟨115⟩)  rfl rfl (by decide) (by decide))
  witness_step (dup3_xstep (code := witnessEnv.code) (pcv := ⟨116⟩) (a := ⟨0⟩) (b := ⟨0⟩) (c := ⟨128⟩) (t := [⟨192⟩, ⟨43⟩]) rfl rfl (by decide) (by with_unfolding_all rfl) (by decide))
  witness_step (mload_xstep (code := witnessEnv.code) (pcv := ⟨117⟩) (a := ⟨128⟩) (t := [⟨0⟩, ⟨0⟩, ⟨128⟩, ⟨192⟩, ⟨43⟩]) rfl rfl (by decide) (by with_unfolding_all rfl) (by decide))
  witness_step (push1_xstep (code := witnessEnv.code) (pcv := ⟨118⟩) (argv := ⟨1⟩) (rest := [⟨1⟩, ⟨0⟩, ⟨0⟩, ⟨128⟩, ⟨192⟩, ⟨43⟩]) rfl rfl (by decide) (by with_unfolding_all rfl) (by decide))
  witness_step (push1_xstep (code := witnessEnv.code) (pcv := ⟨120⟩) (argv := ⟨1⟩) (rest := [⟨1⟩, ⟨1⟩, ⟨0⟩, ⟨0⟩, ⟨128⟩, ⟨192⟩, ⟨43⟩]) rfl rfl (by decide) (by with_unfolding_all rfl) (by decide))
  witness_step (push1_xstep (code := witnessEnv.code) (pcv := ⟨122⟩) (argv := ⟨160⟩) (rest := [⟨1⟩, ⟨1⟩, ⟨1⟩, ⟨0⟩, ⟨0⟩, ⟨128⟩, ⟨192⟩, ⟨43⟩]) rfl rfl (by decide) (by with_unfolding_all rfl) (by decide))
  witness_step (shl_xstep (code := witnessEnv.code) (pcv := ⟨124⟩) (a := ⟨160⟩) (b := ⟨1⟩) (t := [⟨1⟩, ⟨1⟩, ⟨0⟩, ⟨0⟩, ⟨128⟩, ⟨192⟩, ⟨43⟩]) rfl rfl (by decide) (by with_unfolding_all rfl) (by decide))
  witness_step (sub_xstep (code := witnessEnv.code) (pcv := ⟨125⟩) (a := ⟨1461501637330902918203684832716283019655932542976⟩) (b := ⟨1⟩) (t := [⟨1⟩, ⟨0⟩, ⟨0⟩, ⟨128⟩, ⟨192⟩, ⟨43⟩]) rfl rfl (by decide) (by with_unfolding_all rfl) (by decide))
  witness_step (dup2_xstep (code := witnessEnv.code) (pcv := ⟨126⟩) (a := ⟨1461501637330902918203684832716283019655932542975⟩) (b := ⟨1⟩) (t := [⟨0⟩, ⟨0⟩, ⟨128⟩, ⟨192⟩, ⟨43⟩]) rfl rfl (by decide) (by with_unfolding_all rfl) (by decide))
  witness_step (and_xstep (code := witnessEnv.code) (pcv := ⟨127⟩) (a := ⟨1⟩) (b := ⟨1461501637330902918203684832716283019655932542975⟩) (t := [⟨1⟩, ⟨0⟩, ⟨0⟩, ⟨128⟩, ⟨192⟩, ⟨43⟩]) rfl rfl (by decide) (by with_unfolding_all rfl) (by decide))
  witness_step (dup2_xstep (code := witnessEnv.code) (pcv := ⟨128⟩) (a := ⟨1⟩) (b := ⟨1⟩) (t := [⟨0⟩, ⟨0⟩, ⟨128⟩, ⟨192⟩, ⟨43⟩]) rfl rfl (by decide) (by with_unfolding_all rfl) (by decide))
  witness_step (eq_xstep (code := witnessEnv.code) (pcv := ⟨129⟩) (a := ⟨1⟩) (b := ⟨1⟩) (t := [⟨1⟩, ⟨0⟩, ⟨0⟩, ⟨128⟩, ⟨192⟩, ⟨43⟩]) rfl rfl (by decide) (by with_unfolding_all rfl) (by decide))
  witness_step (push1_xstep (code := witnessEnv.code) (pcv := ⟨130⟩) (argv := ⟨136⟩) (rest := [⟨1⟩, ⟨1⟩, ⟨0⟩, ⟨0⟩, ⟨128⟩, ⟨192⟩, ⟨43⟩]) rfl rfl (by decide) (by with_unfolding_all rfl) (by decide))
  witness_step (jumpi_t_xstep (code := witnessEnv.code) (pcv := ⟨132⟩) (a := ⟨136⟩) (b := ⟨1⟩) (t := [⟨1⟩, ⟨0⟩, ⟨0⟩, ⟨128⟩, ⟨192⟩, ⟨43⟩]) rfl rfl (by decide) (by with_unfolding_all rfl) (by decide +kernel) (jumpScan_valid witnessEnv.code 136 170 (by decide)) (by decide))
  witness_step (jumpdest_xstep (code := witnessEnv.code) (pcv := ⟨136⟩)  rfl rfl (by decide) (by decide))
  witness_step (push1_xstep (code := witnessEnv.code) (pcv := ⟨137⟩) (argv := ⟨32⟩) (rest := [⟨1⟩, ⟨0⟩, ⟨0⟩, ⟨128⟩, ⟨192⟩, ⟨43⟩]) rfl rfl (by decide) (by with_unfolding_all rfl) (by decide))
  witness_step (swap4_xstep (code := witnessEnv.code) (pcv := ⟨139⟩) (a := ⟨32⟩) (b := ⟨1⟩) (c := ⟨0⟩) (d := ⟨0⟩) (e := ⟨128⟩) (t := [⟨192⟩, ⟨43⟩]) rfl rfl (by decide) (by with_unfolding_all rfl) (by decide))
  witness_step (swap1_xstep (code := witnessEnv.code) (pcv := ⟨140⟩) (a := ⟨128⟩) (b := ⟨1⟩) (t := [⟨0⟩, ⟨0⟩, ⟨32⟩, ⟨192⟩, ⟨43⟩]) rfl rfl (by decide) (by with_unfolding_all rfl) (by decide))
  witness_step (swap4_xstep (code := witnessEnv.code) (pcv := ⟨141⟩) (a := ⟨1⟩) (b := ⟨128⟩) (c := ⟨0⟩) (d := ⟨0⟩) (e := ⟨32⟩) (t := [⟨192⟩, ⟨43⟩]) rfl rfl (by decide) (by with_unfolding_all rfl) (by decide))
  witness_step (add_xstep (code := witnessEnv.code) (pcv := ⟨142⟩) (a := ⟨32⟩) (b := ⟨128⟩) (t := [⟨0⟩, ⟨0⟩, ⟨1⟩, ⟨192⟩, ⟨43⟩]) rfl rfl (by decide) (by with_unfolding_all rfl) (by decide))
  witness_step (mload_xstep (code := witnessEnv.code) (pcv := ⟨143⟩) (a := ⟨160⟩) (t := [⟨0⟩, ⟨0⟩, ⟨1⟩, ⟨192⟩, ⟨43⟩]) rfl rfl (by decide) (by with_unfolding_all rfl) (by decide))
  witness_step (swap3_xstep (code := witnessEnv.code) (pcv := ⟨144⟩) (a := ⟨1⟩) (b := ⟨0⟩) (c := ⟨0⟩) (d := ⟨1⟩) (t := [⟨192⟩, ⟨43⟩]) rfl rfl (by decide) (by with_unfolding_all rfl) (by decide))
  witness_step (swap5_xstep (code := witnessEnv.code) (pcv := ⟨145⟩) (a := ⟨1⟩) (b := ⟨0⟩) (c := ⟨0⟩) (d := ⟨1⟩) (e := ⟨192⟩) (f := ⟨43⟩) (t := []) rfl rfl (by decide) (by with_unfolding_all rfl) (by decide))
  witness_step (swap3_xstep (code := witnessEnv.code) (pcv := ⟨146⟩) (a := ⟨43⟩) (b := ⟨0⟩) (c := ⟨0⟩) (d := ⟨1⟩) (t := [⟨192⟩, ⟨1⟩]) rfl rfl (by decide) (by with_unfolding_all rfl) (by decide))
  witness_step (swap4_xstep (code := witnessEnv.code) (pcv := ⟨147⟩) (a := ⟨1⟩) (b := ⟨0⟩) (c := ⟨0⟩) (d := ⟨43⟩) (e := ⟨192⟩) (t := [⟨1⟩]) rfl rfl (by decide) (by with_unfolding_all rfl) (by decide))
  witness_step (pop_xstep (code := witnessEnv.code) (pcv := ⟨148⟩) (a := ⟨192⟩) (t := [⟨0⟩, ⟨0⟩, ⟨43⟩, ⟨1⟩, ⟨1⟩]) rfl rfl (by decide) (by with_unfolding_all rfl) (by decide))
  witness_step (pop_xstep (code := witnessEnv.code) (pcv := ⟨149⟩) (a := ⟨0⟩) (t := [⟨0⟩, ⟨43⟩, ⟨1⟩, ⟨1⟩]) rfl rfl (by decide) (by with_unfolding_all rfl) (by decide))
  witness_step (pop_xstep (code := witnessEnv.code) (pcv := ⟨150⟩) (a := ⟨0⟩) (t := [⟨43⟩, ⟨1⟩, ⟨1⟩]) rfl rfl (by decide) (by with_unfolding_all rfl) (by decide))
  witness_step (jump_xstep (code := witnessEnv.code) (pcv := ⟨151⟩) (a := ⟨43⟩) (t := [⟨1⟩, ⟨1⟩]) rfl rfl (by decide) (by with_unfolding_all rfl) (jumpScan_valid witnessEnv.code 43 170 (by decide)) (by decide))
  witness_step (jumpdest_xstep (code := witnessEnv.code) (pcv := ⟨43⟩)  rfl rfl (by decide) (by decide))
  witness_step (push1_xstep (code := witnessEnv.code) (pcv := ⟨44⟩) (argv := ⟨1⟩) (rest := [⟨1⟩, ⟨1⟩]) rfl rfl (by decide) (by with_unfolding_all rfl) (by decide))
  witness_step (push1_xstep (code := witnessEnv.code) (pcv := ⟨46⟩) (argv := ⟨1⟩) (rest := [⟨1⟩, ⟨1⟩, ⟨1⟩]) rfl rfl (by decide) (by with_unfolding_all rfl) (by decide))
  witness_step (push1_xstep (code := witnessEnv.code) (pcv := ⟨48⟩) (argv := ⟨160⟩) (rest := [⟨1⟩, ⟨1⟩, ⟨1⟩, ⟨1⟩]) rfl rfl (by decide) (by with_unfolding_all rfl) (by decide))
  witness_step (shl_xstep (code := witnessEnv.code) (pcv := ⟨50⟩) (a := ⟨160⟩) (b := ⟨1⟩) (t := [⟨1⟩, ⟨1⟩, ⟨1⟩]) rfl rfl (by decide) (by with_unfolding_all rfl) (by decide))
  witness_step (sub_xstep (code := witnessEnv.code) (pcv := ⟨51⟩) (a := ⟨1461501637330902918203684832716283019655932542976⟩) (b := ⟨1⟩) (t := [⟨1⟩, ⟨1⟩]) rfl rfl (by decide) (by with_unfolding_all rfl) (by decide))
  witness_step (dup3_xstep (code := witnessEnv.code) (pcv := ⟨52⟩) (a := ⟨1461501637330902918203684832716283019655932542975⟩) (b := ⟨1⟩) (c := ⟨1⟩) (t := []) rfl rfl (by decide) (by with_unfolding_all rfl) (by decide))
  witness_step (and_xstep (code := witnessEnv.code) (pcv := ⟨53⟩) (a := ⟨1⟩) (b := ⟨1461501637330902918203684832716283019655932542975⟩) (t := [⟨1⟩, ⟨1⟩]) rfl rfl (by decide) (by with_unfolding_all rfl) (by decide))
  witness_step (push1_xstep (code := witnessEnv.code) (pcv := ⟨54⟩) (argv := ⟨60⟩) (rest := [⟨1⟩, ⟨1⟩, ⟨1⟩]) rfl rfl (by decide) (by with_unfolding_all rfl) (by decide))
  witness_step (jumpi_t_xstep (code := witnessEnv.code) (pcv := ⟨56⟩) (a := ⟨60⟩) (b := ⟨1⟩) (t := [⟨1⟩, ⟨1⟩]) rfl rfl (by decide) (by with_unfolding_all rfl) (by decide +kernel) (jumpScan_valid witnessEnv.code 60 170 (by decide)) (by decide))
  witness_step (jumpdest_xstep (code := witnessEnv.code) (pcv := ⟨60⟩)  rfl rfl (by decide) (by decide))
  witness_step (push0_xstep (code := witnessEnv.code) (pcv := ⟨61⟩) (rest := [⟨1⟩, ⟨1⟩]) rfl rfl (by decide) (by with_unfolding_all rfl) (by decide))
  witness_step (dup1_xstep (code := witnessEnv.code) (pcv := ⟨62⟩) (a := ⟨0⟩) (t := [⟨1⟩, ⟨1⟩]) rfl rfl (by decide) (by with_unfolding_all rfl) (by decide))
  witness_step (sload_xstep (code := witnessEnv.code) (pcv := ⟨63⟩) (a := ⟨0⟩) (t := [⟨0⟩, ⟨1⟩, ⟨1⟩]) rfl rfl (by decide) (by with_unfolding_all rfl) (by decide))
  witness_step (push1_xstep (code := witnessEnv.code) (pcv := ⟨64⟩) (argv := ⟨1⟩) (rest := [⟨0⟩, ⟨0⟩, ⟨1⟩, ⟨1⟩]) rfl rfl (by decide) (by with_unfolding_all rfl) (by decide))
  witness_step (push1_xstep (code := witnessEnv.code) (pcv := ⟨66⟩) (argv := ⟨1⟩) (rest := [⟨1⟩, ⟨0⟩, ⟨0⟩, ⟨1⟩, ⟨1⟩]) rfl rfl (by decide) (by with_unfolding_all rfl) (by decide))
  witness_step (push1_xstep (code := witnessEnv.code) (pcv := ⟨68⟩) (argv := ⟨160⟩) (rest := [⟨1⟩, ⟨1⟩, ⟨0⟩, ⟨0⟩, ⟨1⟩, ⟨1⟩]) rfl rfl (by decide) (by with_unfolding_all rfl) (by decide))
  witness_step (shl_xstep (code := witnessEnv.code) (pcv := ⟨70⟩) (a := ⟨160⟩) (b := ⟨1⟩) (t := [⟨1⟩, ⟨0⟩, ⟨0⟩, ⟨1⟩, ⟨1⟩]) rfl rfl (by decide) (by with_unfolding_all rfl) (by decide))
  witness_step (sub_xstep (code := witnessEnv.code) (pcv := ⟨71⟩) (a := ⟨1461501637330902918203684832716283019655932542976⟩) (b := ⟨1⟩) (t := [⟨0⟩, ⟨0⟩, ⟨1⟩, ⟨1⟩]) rfl rfl (by decide) (by with_unfolding_all rfl) (by decide))
  witness_step (not_xstep (code := witnessEnv.code) (pcv := ⟨72⟩) (a := ⟨1461501637330902918203684832716283019655932542975⟩) (t := [⟨0⟩, ⟨0⟩, ⟨1⟩, ⟨1⟩]) rfl rfl (by decide) (by with_unfolding_all rfl) (by decide))
  witness_step (and_xstep (code := witnessEnv.code) (pcv := ⟨73⟩) (a := ⟨115792089237316195423570985007226406215939081747436879206741300988257197096960⟩) (b := ⟨0⟩) (t := [⟨0⟩, ⟨1⟩, ⟨1⟩]) rfl rfl (by decide) (by with_unfolding_all rfl) (by decide))
  witness_step (push1_xstep (code := witnessEnv.code) (pcv := ⟨74⟩) (argv := ⟨1⟩) (rest := [⟨0⟩, ⟨0⟩, ⟨1⟩, ⟨1⟩]) rfl rfl (by decide) (by with_unfolding_all rfl) (by decide))
  witness_step (push1_xstep (code := witnessEnv.code) (pcv := ⟨76⟩) (argv := ⟨1⟩) (rest := [⟨1⟩, ⟨0⟩, ⟨0⟩, ⟨1⟩, ⟨1⟩]) rfl rfl (by decide) (by with_unfolding_all rfl) (by decide))
  witness_step (push1_xstep (code := witnessEnv.code) (pcv := ⟨78⟩) (argv := ⟨160⟩) (rest := [⟨1⟩, ⟨1⟩, ⟨0⟩, ⟨0⟩, ⟨1⟩, ⟨1⟩]) rfl rfl (by decide) (by with_unfolding_all rfl) (by decide))
  witness_step (shl_xstep (code := witnessEnv.code) (pcv := ⟨80⟩) (a := ⟨160⟩) (b := ⟨1⟩) (t := [⟨1⟩, ⟨0⟩, ⟨0⟩, ⟨1⟩, ⟨1⟩]) rfl rfl (by decide) (by with_unfolding_all rfl) (by decide))
  witness_step (sub_xstep (code := witnessEnv.code) (pcv := ⟨81⟩) (a := ⟨1461501637330902918203684832716283019655932542976⟩) (b := ⟨1⟩) (t := [⟨0⟩, ⟨0⟩, ⟨1⟩, ⟨1⟩]) rfl rfl (by decide) (by with_unfolding_all rfl) (by decide))
  witness_step (swap4_xstep (code := witnessEnv.code) (pcv := ⟨82⟩) (a := ⟨1461501637330902918203684832716283019655932542975⟩) (b := ⟨0⟩) (c := ⟨0⟩) (d := ⟨1⟩) (e := ⟨1⟩) (t := []) rfl rfl (by decide) (by with_unfolding_all rfl) (by decide))
  witness_step (swap1_xstep (code := witnessEnv.code) (pcv := ⟨83⟩) (a := ⟨1⟩) (b := ⟨0⟩) (t := [⟨0⟩, ⟨1⟩, ⟨1461501637330902918203684832716283019655932542975⟩]) rfl rfl (by decide) (by with_unfolding_all rfl) (by decide))
  witness_step (swap4_xstep (code := witnessEnv.code) (pcv := ⟨84⟩) (a := ⟨0⟩) (b := ⟨1⟩) (c := ⟨0⟩) (d := ⟨1⟩) (e := ⟨1461501637330902918203684832716283019655932542975⟩) (t := []) rfl rfl (by decide) (by with_unfolding_all rfl) (by decide))
  witness_step (and_xstep (code := witnessEnv.code) (pcv := ⟨85⟩) (a := ⟨1461501637330902918203684832716283019655932542975⟩) (b := ⟨1⟩) (t := [⟨0⟩, ⟨1⟩, ⟨0⟩]) rfl rfl (by decide) (by with_unfolding_all rfl) (by decide))
  witness_step (swap3_xstep (code := witnessEnv.code) (pcv := ⟨86⟩) (a := ⟨1⟩) (b := ⟨0⟩) (c := ⟨1⟩) (d := ⟨0⟩) (t := []) rfl rfl (by decide) (by with_unfolding_all rfl) (by decide))
  witness_step (swap1_xstep (code := witnessEnv.code) (pcv := ⟨87⟩) (a := ⟨0⟩) (b := ⟨0⟩) (t := [⟨1⟩, ⟨1⟩]) rfl rfl (by decide) (by with_unfolding_all rfl) (by decide))
  witness_step (swap3_xstep (code := witnessEnv.code) (pcv := ⟨88⟩) (a := ⟨0⟩) (b := ⟨0⟩) (c := ⟨1⟩) (d := ⟨1⟩) (t := []) rfl rfl (by decide) (by with_unfolding_all rfl) (by decide))
  witness_step (or_xstep (code := witnessEnv.code) (pcv := ⟨89⟩) (a := ⟨1⟩) (b := ⟨0⟩) (t := [⟨1⟩, ⟨0⟩]) rfl rfl (by decide) (by with_unfolding_all rfl) (by decide))
  witness_step (swap1_xstep (code := witnessEnv.code) (pcv := ⟨90⟩) (a := ⟨1⟩) (b := ⟨1⟩) (t := [⟨0⟩]) rfl rfl (by decide) (by with_unfolding_all rfl) (by decide))
  witness_step (swap2_xstep (code := witnessEnv.code) (pcv := ⟨91⟩) (a := ⟨1⟩) (b := ⟨1⟩) (c := ⟨0⟩) (t := []) rfl rfl (by decide) (by with_unfolding_all rfl) (by decide))
  witness_step (sstore_xstep (code := witnessEnv.code) (pcv := ⟨92⟩) (slot := ⟨0⟩) (val := ⟨1⟩) (t := [⟨1⟩]) rfl rfl (by decide) rfl (by with_unfolding_all rfl) (by decide))
  witness_step (push1_xstep (code := witnessEnv.code) (pcv := ⟨93⟩) (argv := ⟨1⟩) (rest := [⟨1⟩]) rfl rfl (by decide) (by with_unfolding_all rfl) (by decide))
  witness_step (sstore_xstep (code := witnessEnv.code) (pcv := ⟨95⟩) (slot := ⟨1⟩) (val := ⟨1⟩) (t := []) rfl rfl (by decide) rfl (by with_unfolding_all rfl) (by decide))
  witness_step (push1_xstep (code := witnessEnv.code) (pcv := ⟨96⟩) (argv := ⟨152⟩) (rest := []) rfl rfl (by decide) (by with_unfolding_all rfl) (by decide))
  witness_step (jump_xstep (code := witnessEnv.code) (pcv := ⟨98⟩) (a := ⟨152⟩) (t := []) rfl rfl (by decide) (by with_unfolding_all rfl) (jumpScan_valid witnessEnv.code 152 170 (by decide)) (by decide))
  witness_step (jumpdest_xstep (code := witnessEnv.code) (pcv := ⟨152⟩)  rfl rfl (by decide) (by decide))
  witness_step (push2_xstep (code := witnessEnv.code) (pcv := ⟨153⟩) (argv := ⟨1429⟩) (rest := []) rfl rfl (by decide) (by with_unfolding_all rfl) (by decide))
  witness_step (dup1_xstep (code := witnessEnv.code) (pcv := ⟨156⟩) (a := ⟨1429⟩) (t := []) rfl rfl (by decide) (by with_unfolding_all rfl) (by decide))
  witness_step (push2_xstep (code := witnessEnv.code) (pcv := ⟨157⟩) (argv := ⟨165⟩) (rest := [⟨1429⟩, ⟨1429⟩]) rfl rfl (by decide) (by with_unfolding_all rfl) (by decide))
  witness_step (push0_xstep (code := witnessEnv.code) (pcv := ⟨160⟩) (rest := [⟨165⟩, ⟨1429⟩, ⟨1429⟩]) rfl rfl (by decide) (by with_unfolding_all rfl) (by decide))
  witness_step (codecopy_xstep (code := witnessEnv.code) (pcv := ⟨161⟩) (a := ⟨0⟩) (b := ⟨165⟩) (c := ⟨1429⟩) (t := [⟨1429⟩]) rfl rfl (by decide) (by with_unfolding_all rfl) (by decide))
  witness_step (push0_xstep (code := witnessEnv.code) (pcv := ⟨162⟩) (rest := [⟨1429⟩]) rfl rfl (by decide) (by with_unfolding_all rfl) (by decide))
  apply execution_return
  · rw [return_xstep (code := witnessEnv.code) (pcv := ⟨163⟩) (a := ⟨0⟩) (b := ⟨1429⟩) (t := []) rfl rfl (by decide) (by with_unfolding_all rfl) (by decide)]
    with_unfolding_all rfl
  · decide +kernel

end CreationWitness

end Rollup.EVM
