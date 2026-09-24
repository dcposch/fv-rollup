import proofs.RuntimeBytecode
import proofs.generated.KeccakMappingOne
import proofs.HashComputation
open Ethereum Ethereum.EVM Reasoning.Theory
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
namespace Rollup.EVM
namespace DepositWitness

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
    code := runtimeBytecode, calldata := ⟨#[243, 64, 250, 1] ++ (Array.replicate 31 0).push 1⟩, weiValue := ⟨1⟩, perm := true }
noncomputable def witnessStart : Ethereum.State :=
  initState default default default
    ((default : AccountMap).insert 42 { (default : Account) with nonce := ⟨1⟩, balance := ⟨1⟩, code := runtimeBytecode }) default
    (1000000 : Sat256) default witnessEnv

macro "deposit_witness_step " step:term : tactic =>
  `(tactic| (
    apply execution_step
    · rw [($step)]
      with_unfolding_all rfl))

private theorem witness_hash {bytes : ByteArray}
    (input : bytes = ⟨#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4]⟩) :
    Ethereum.KEC bytes = ⟨#[171, 214, 231, 203, 80, 152, 79, 249, 194, 243, 225, 138, 38, 96, 195, 53, 61, 173, 244, 227, 41, 29, 238, 178, 117, 218, 226, 205, 30, 68, 254, 5]⟩ := by
  rw [input, HashCertificates.deposit_mapping_one]

/-- This deposit run succeeds with one wei. -/
theorem executes : ∃ final output, X 1000001 (D_J witnessEnv.code 0) witnessStart =
    .ok (.success final output) ∧ output = ByteArray.empty := by
  deposit_witness_step (push1_xstep (code := witnessEnv.code) (pcv := ⟨0⟩) (argv := ⟨128⟩) (rest := []) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (push1_xstep (code := witnessEnv.code) (pcv := ⟨2⟩) (argv := ⟨64⟩) (rest := [⟨128⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (mstore_xstep (code := witnessEnv.code) (pcv := ⟨4⟩) (a := ⟨64⟩) (b := ⟨128⟩) (t := []) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (push1_xstep (code := witnessEnv.code) (pcv := ⟨5⟩) (argv := ⟨4⟩) (rest := []) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (calldatasize_xstep (code := witnessEnv.code) (pcv := ⟨7⟩) (rest := [⟨4⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (lt_xstep (code := witnessEnv.code) (pcv := ⟨8⟩) (a := ⟨36⟩) (b := ⟨4⟩) (t := []) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (push2_xstep (code := witnessEnv.code) (pcv := ⟨9⟩) (argv := ⟨132⟩) (rest := [⟨0⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (jumpi_nt_xstep (code := witnessEnv.code) (pcv := ⟨12⟩) (a := ⟨132⟩) (t := []) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (push0_xstep (code := witnessEnv.code) (pcv := ⟨13⟩) (rest := []) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (calldataload_xstep (code := witnessEnv.code) (pcv := ⟨14⟩) (a := ⟨0⟩) (t := []) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (push1_xstep (code := witnessEnv.code) (pcv := ⟨15⟩) (argv := ⟨224⟩) (rest := [⟨110026825881426193279908600449895606160991820677118730779328024479053578764288⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (shr_xstep (code := witnessEnv.code) (pcv := ⟨17⟩) (a := ⟨224⟩) (b := ⟨110026825881426193279908600449895606160991820677118730779328024479053578764288⟩) (t := []) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (dup1_xstep (code := witnessEnv.code) (pcv := ⟨18⟩) (a := ⟨4081121793⟩) (t := []) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (push4_xstep (code := witnessEnv.code) (pcv := ⟨19⟩) (argv := ⟨3141465730⟩) (rest := [⟨4081121793⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (gt_xstep (code := witnessEnv.code) (pcv := ⟨24⟩) (a := ⟨3141465730⟩) (b := ⟨4081121793⟩) (t := [⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (push2_xstep (code := witnessEnv.code) (pcv := ⟨25⟩) (argv := ⟨87⟩) (rest := [⟨0⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (jumpi_nt_xstep (code := witnessEnv.code) (pcv := ⟨28⟩) (a := ⟨87⟩) (t := [⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (dup1_xstep (code := witnessEnv.code) (pcv := ⟨29⟩) (a := ⟨4081121793⟩) (t := []) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (push4_xstep (code := witnessEnv.code) (pcv := ⟨30⟩) (argv := ⟨3141465730⟩) (rest := [⟨4081121793⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (eq_xstep (code := witnessEnv.code) (pcv := ⟨35⟩) (a := ⟨3141465730⟩) (b := ⟨4081121793⟩) (t := [⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (push2_xstep (code := witnessEnv.code) (pcv := ⟨36⟩) (argv := ⟨284⟩) (rest := [⟨0⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (jumpi_nt_xstep (code := witnessEnv.code) (pcv := ⟨39⟩) (a := ⟨284⟩) (t := [⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (dup1_xstep (code := witnessEnv.code) (pcv := ⟨40⟩) (a := ⟨4081121793⟩) (t := []) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (push4_xstep (code := witnessEnv.code) (pcv := ⟨41⟩) (argv := ⟨3377479650⟩) (rest := [⟨4081121793⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (eq_xstep (code := witnessEnv.code) (pcv := ⟨46⟩) (a := ⟨3377479650⟩) (b := ⟨4081121793⟩) (t := [⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (push2_xstep (code := witnessEnv.code) (pcv := ⟨47⟩) (argv := ⟨315⟩) (rest := [⟨0⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (jumpi_nt_xstep (code := witnessEnv.code) (pcv := ⟨50⟩) (a := ⟨315⟩) (t := [⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (dup1_xstep (code := witnessEnv.code) (pcv := ⟨51⟩) (a := ⟨4081121793⟩) (t := []) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (push4_xstep (code := witnessEnv.code) (pcv := ⟨52⟩) (argv := ⟨3946006969⟩) (rest := [⟨4081121793⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (eq_xstep (code := witnessEnv.code) (pcv := ⟨57⟩) (a := ⟨3946006969⟩) (b := ⟨4081121793⟩) (t := [⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (push2_xstep (code := witnessEnv.code) (pcv := ⟨58⟩) (argv := ⟨336⟩) (rest := [⟨0⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (jumpi_nt_xstep (code := witnessEnv.code) (pcv := ⟨61⟩) (a := ⟨336⟩) (t := [⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (dup1_xstep (code := witnessEnv.code) (pcv := ⟨62⟩) (a := ⟨4081121793⟩) (t := []) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (push4_xstep (code := witnessEnv.code) (pcv := ⟨63⟩) (argv := ⟨4081121793⟩) (rest := [⟨4081121793⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (eq_xstep (code := witnessEnv.code) (pcv := ⟨68⟩) (a := ⟨4081121793⟩) (b := ⟨4081121793⟩) (t := [⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (push2_xstep (code := witnessEnv.code) (pcv := ⟨69⟩) (argv := ⟨379⟩) (rest := [⟨1⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (jumpi_t_xstep (code := witnessEnv.code) (pcv := ⟨72⟩) (a := ⟨379⟩) (b := ⟨1⟩) (t := [⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel) (jumpScan_valid witnessEnv.code 379 1429 (by decide +kernel)) (by decide +kernel))
  deposit_witness_step (jumpdest_xstep (code := witnessEnv.code) (pcv := ⟨379⟩)  rfl rfl (by decide +kernel) (by decide +kernel))
  deposit_witness_step (push2_xstep (code := witnessEnv.code) (pcv := ⟨380⟩) (argv := ⟨226⟩) (rest := [⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (push2_xstep (code := witnessEnv.code) (pcv := ⟨383⟩) (argv := ⟨393⟩) (rest := [⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (calldatasize_xstep (code := witnessEnv.code) (pcv := ⟨386⟩) (rest := [⟨393⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (push1_xstep (code := witnessEnv.code) (pcv := ⟨387⟩) (argv := ⟨4⟩) (rest := [⟨36⟩, ⟨393⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (push2_xstep (code := witnessEnv.code) (pcv := ⟨389⟩) (argv := ⟨1331⟩) (rest := [⟨4⟩, ⟨36⟩, ⟨393⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (jump_xstep (code := witnessEnv.code) (pcv := ⟨392⟩) (a := ⟨1331⟩) (t := [⟨4⟩, ⟨36⟩, ⟨393⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (jumpScan_valid witnessEnv.code 1331 1429 (by decide +kernel)) (by decide +kernel))
  deposit_witness_step (jumpdest_xstep (code := witnessEnv.code) (pcv := ⟨1331⟩)  rfl rfl (by decide +kernel) (by decide +kernel))
  deposit_witness_step (push0_xstep (code := witnessEnv.code) (pcv := ⟨1332⟩) (rest := [⟨4⟩, ⟨36⟩, ⟨393⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (push1_xstep (code := witnessEnv.code) (pcv := ⟨1333⟩) (argv := ⟨32⟩) (rest := [⟨0⟩, ⟨4⟩, ⟨36⟩, ⟨393⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (dup3_xstep (code := witnessEnv.code) (pcv := ⟨1335⟩) (a := ⟨32⟩) (b := ⟨0⟩) (c := ⟨4⟩) (t := [⟨36⟩, ⟨393⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (dup5_xstep (code := witnessEnv.code) (pcv := ⟨1336⟩) (a := ⟨4⟩) (b := ⟨32⟩) (c := ⟨0⟩) (d := ⟨4⟩) (e := ⟨36⟩) (t := [⟨393⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (sub_xstep (code := witnessEnv.code) (pcv := ⟨1337⟩) (a := ⟨36⟩) (b := ⟨4⟩) (t := [⟨32⟩, ⟨0⟩, ⟨4⟩, ⟨36⟩, ⟨393⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (slt_xstep (code := witnessEnv.code) (pcv := ⟨1338⟩) (a := ⟨32⟩) (b := ⟨32⟩) (t := [⟨0⟩, ⟨4⟩, ⟨36⟩, ⟨393⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (iszero_xstep (code := witnessEnv.code) (pcv := ⟨1339⟩) (a := ⟨0⟩) (t := [⟨0⟩, ⟨4⟩, ⟨36⟩, ⟨393⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (push2_xstep (code := witnessEnv.code) (pcv := ⟨1340⟩) (argv := ⟨1347⟩) (rest := [⟨1⟩, ⟨0⟩, ⟨4⟩, ⟨36⟩, ⟨393⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (jumpi_t_xstep (code := witnessEnv.code) (pcv := ⟨1343⟩) (a := ⟨1347⟩) (b := ⟨1⟩) (t := [⟨0⟩, ⟨4⟩, ⟨36⟩, ⟨393⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel) (jumpScan_valid witnessEnv.code 1347 1429 (by decide +kernel)) (by decide +kernel))
  deposit_witness_step (jumpdest_xstep (code := witnessEnv.code) (pcv := ⟨1347⟩)  rfl rfl (by decide +kernel) (by decide +kernel))
  deposit_witness_step (dup2_xstep (code := witnessEnv.code) (pcv := ⟨1348⟩) (a := ⟨0⟩) (b := ⟨4⟩) (t := [⟨36⟩, ⟨393⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (calldataload_xstep (code := witnessEnv.code) (pcv := ⟨1349⟩) (a := ⟨4⟩) (t := [⟨0⟩, ⟨4⟩, ⟨36⟩, ⟨393⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (push2_xstep (code := witnessEnv.code) (pcv := ⟨1350⟩) (argv := ⟨1358⟩) (rest := [⟨1⟩, ⟨0⟩, ⟨4⟩, ⟨36⟩, ⟨393⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (dup2_xstep (code := witnessEnv.code) (pcv := ⟨1353⟩) (a := ⟨1358⟩) (b := ⟨1⟩) (t := [⟨0⟩, ⟨4⟩, ⟨36⟩, ⟨393⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (push2_xstep (code := witnessEnv.code) (pcv := ⟨1354⟩) (argv := ⟨1165⟩) (rest := [⟨1⟩, ⟨1358⟩, ⟨1⟩, ⟨0⟩, ⟨4⟩, ⟨36⟩, ⟨393⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (jump_xstep (code := witnessEnv.code) (pcv := ⟨1357⟩) (a := ⟨1165⟩) (t := [⟨1⟩, ⟨1358⟩, ⟨1⟩, ⟨0⟩, ⟨4⟩, ⟨36⟩, ⟨393⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (jumpScan_valid witnessEnv.code 1165 1429 (by decide +kernel)) (by decide +kernel))
  deposit_witness_step (jumpdest_xstep (code := witnessEnv.code) (pcv := ⟨1165⟩)  rfl rfl (by decide +kernel) (by decide +kernel))
  deposit_witness_step (push1_xstep (code := witnessEnv.code) (pcv := ⟨1166⟩) (argv := ⟨1⟩) (rest := [⟨1⟩, ⟨1358⟩, ⟨1⟩, ⟨0⟩, ⟨4⟩, ⟨36⟩, ⟨393⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (push1_xstep (code := witnessEnv.code) (pcv := ⟨1168⟩) (argv := ⟨1⟩) (rest := [⟨1⟩, ⟨1⟩, ⟨1358⟩, ⟨1⟩, ⟨0⟩, ⟨4⟩, ⟨36⟩, ⟨393⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (push1_xstep (code := witnessEnv.code) (pcv := ⟨1170⟩) (argv := ⟨160⟩) (rest := [⟨1⟩, ⟨1⟩, ⟨1⟩, ⟨1358⟩, ⟨1⟩, ⟨0⟩, ⟨4⟩, ⟨36⟩, ⟨393⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (shl_xstep (code := witnessEnv.code) (pcv := ⟨1172⟩) (a := ⟨160⟩) (b := ⟨1⟩) (t := [⟨1⟩, ⟨1⟩, ⟨1358⟩, ⟨1⟩, ⟨0⟩, ⟨4⟩, ⟨36⟩, ⟨393⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (sub_xstep (code := witnessEnv.code) (pcv := ⟨1173⟩) (a := ⟨1461501637330902918203684832716283019655932542976⟩) (b := ⟨1⟩) (t := [⟨1⟩, ⟨1358⟩, ⟨1⟩, ⟨0⟩, ⟨4⟩, ⟨36⟩, ⟨393⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (dup2_xstep (code := witnessEnv.code) (pcv := ⟨1174⟩) (a := ⟨1461501637330902918203684832716283019655932542975⟩) (b := ⟨1⟩) (t := [⟨1358⟩, ⟨1⟩, ⟨0⟩, ⟨4⟩, ⟨36⟩, ⟨393⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (and_xstep (code := witnessEnv.code) (pcv := ⟨1175⟩) (a := ⟨1⟩) (b := ⟨1461501637330902918203684832716283019655932542975⟩) (t := [⟨1⟩, ⟨1358⟩, ⟨1⟩, ⟨0⟩, ⟨4⟩, ⟨36⟩, ⟨393⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (dup2_xstep (code := witnessEnv.code) (pcv := ⟨1176⟩) (a := ⟨1⟩) (b := ⟨1⟩) (t := [⟨1358⟩, ⟨1⟩, ⟨0⟩, ⟨4⟩, ⟨36⟩, ⟨393⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (eq_xstep (code := witnessEnv.code) (pcv := ⟨1177⟩) (a := ⟨1⟩) (b := ⟨1⟩) (t := [⟨1⟩, ⟨1358⟩, ⟨1⟩, ⟨0⟩, ⟨4⟩, ⟨36⟩, ⟨393⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (push2_xstep (code := witnessEnv.code) (pcv := ⟨1178⟩) (argv := ⟨1185⟩) (rest := [⟨1⟩, ⟨1⟩, ⟨1358⟩, ⟨1⟩, ⟨0⟩, ⟨4⟩, ⟨36⟩, ⟨393⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (jumpi_t_xstep (code := witnessEnv.code) (pcv := ⟨1181⟩) (a := ⟨1185⟩) (b := ⟨1⟩) (t := [⟨1⟩, ⟨1358⟩, ⟨1⟩, ⟨0⟩, ⟨4⟩, ⟨36⟩, ⟨393⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel) (jumpScan_valid witnessEnv.code 1185 1429 (by decide +kernel)) (by decide +kernel))
  deposit_witness_step (jumpdest_xstep (code := witnessEnv.code) (pcv := ⟨1185⟩)  rfl rfl (by decide +kernel) (by decide +kernel))
  deposit_witness_step (pop_xstep (code := witnessEnv.code) (pcv := ⟨1186⟩) (a := ⟨1⟩) (t := [⟨1358⟩, ⟨1⟩, ⟨0⟩, ⟨4⟩, ⟨36⟩, ⟨393⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (jump_xstep (code := witnessEnv.code) (pcv := ⟨1187⟩) (a := ⟨1358⟩) (t := [⟨1⟩, ⟨0⟩, ⟨4⟩, ⟨36⟩, ⟨393⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (jumpScan_valid witnessEnv.code 1358 1429 (by decide +kernel)) (by decide +kernel))
  deposit_witness_step (jumpdest_xstep (code := witnessEnv.code) (pcv := ⟨1358⟩)  rfl rfl (by decide +kernel) (by decide +kernel))
  deposit_witness_step (swap4_xstep (code := witnessEnv.code) (pcv := ⟨1359⟩) (a := ⟨1⟩) (b := ⟨0⟩) (c := ⟨4⟩) (d := ⟨36⟩) (e := ⟨393⟩) (t := [⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (swap3_xstep (code := witnessEnv.code) (pcv := ⟨1360⟩) (a := ⟨393⟩) (b := ⟨0⟩) (c := ⟨4⟩) (d := ⟨36⟩) (t := [⟨1⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (pop_xstep (code := witnessEnv.code) (pcv := ⟨1361⟩) (a := ⟨36⟩) (t := [⟨0⟩, ⟨4⟩, ⟨393⟩, ⟨1⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (pop_xstep (code := witnessEnv.code) (pcv := ⟨1362⟩) (a := ⟨0⟩) (t := [⟨4⟩, ⟨393⟩, ⟨1⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (pop_xstep (code := witnessEnv.code) (pcv := ⟨1363⟩) (a := ⟨4⟩) (t := [⟨393⟩, ⟨1⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (jump_xstep (code := witnessEnv.code) (pcv := ⟨1364⟩) (a := ⟨393⟩) (t := [⟨1⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (jumpScan_valid witnessEnv.code 393 1429 (by decide +kernel)) (by decide +kernel))
  deposit_witness_step (jumpdest_xstep (code := witnessEnv.code) (pcv := ⟨393⟩)  rfl rfl (by decide +kernel) (by decide +kernel))
  deposit_witness_step (push2_xstep (code := witnessEnv.code) (pcv := ⟨394⟩) (argv := ⟨1045⟩) (rest := [⟨1⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (jump_xstep (code := witnessEnv.code) (pcv := ⟨397⟩) (a := ⟨1045⟩) (t := [⟨1⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (jumpScan_valid witnessEnv.code 1045 1429 (by decide +kernel)) (by decide +kernel))
  deposit_witness_step (jumpdest_xstep (code := witnessEnv.code) (pcv := ⟨1045⟩)  rfl rfl (by decide +kernel) (by decide +kernel))
  deposit_witness_step (push1_xstep (code := witnessEnv.code) (pcv := ⟨1046⟩) (argv := ⟨6⟩) (rest := [⟨1⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (sload_xstep (code := witnessEnv.code) (pcv := ⟨1048⟩) (a := ⟨6⟩) (t := [⟨1⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (iszero_xstep (code := witnessEnv.code) (pcv := ⟨1049⟩) (a := ⟨0⟩) (t := [⟨1⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (push2_xstep (code := witnessEnv.code) (pcv := ⟨1050⟩) (argv := ⟨1057⟩) (rest := [⟨1⟩, ⟨1⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (jumpi_t_xstep (code := witnessEnv.code) (pcv := ⟨1053⟩) (a := ⟨1057⟩) (b := ⟨1⟩) (t := [⟨1⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel) (jumpScan_valid witnessEnv.code 1057 1429 (by decide +kernel)) (by decide +kernel))
  deposit_witness_step (jumpdest_xstep (code := witnessEnv.code) (pcv := ⟨1057⟩)  rfl rfl (by decide +kernel) (by decide +kernel))
  deposit_witness_step (push1_xstep (code := witnessEnv.code) (pcv := ⟨1058⟩) (argv := ⟨1⟩) (rest := [⟨1⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (push1_xstep (code := witnessEnv.code) (pcv := ⟨1060⟩) (argv := ⟨6⟩) (rest := [⟨1⟩, ⟨1⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (sstore_xstep (code := witnessEnv.code) (pcv := ⟨1062⟩) (slot := ⟨6⟩) (val := ⟨1⟩) (t := [⟨1⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) rfl (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (push1_xstep (code := witnessEnv.code) (pcv := ⟨1063⟩) (argv := ⟨1⟩) (rest := [⟨1⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (push1_xstep (code := witnessEnv.code) (pcv := ⟨1065⟩) (argv := ⟨1⟩) (rest := [⟨1⟩, ⟨1⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (push1_xstep (code := witnessEnv.code) (pcv := ⟨1067⟩) (argv := ⟨160⟩) (rest := [⟨1⟩, ⟨1⟩, ⟨1⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (shl_xstep (code := witnessEnv.code) (pcv := ⟨1069⟩) (a := ⟨160⟩) (b := ⟨1⟩) (t := [⟨1⟩, ⟨1⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (sub_xstep (code := witnessEnv.code) (pcv := ⟨1070⟩) (a := ⟨1461501637330902918203684832716283019655932542976⟩) (b := ⟨1⟩) (t := [⟨1⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (dup2_xstep (code := witnessEnv.code) (pcv := ⟨1071⟩) (a := ⟨1461501637330902918203684832716283019655932542975⟩) (b := ⟨1⟩) (t := [⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (and_xstep (code := witnessEnv.code) (pcv := ⟨1072⟩) (a := ⟨1⟩) (b := ⟨1461501637330902918203684832716283019655932542975⟩) (t := [⟨1⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (iszero_xstep (code := witnessEnv.code) (pcv := ⟨1073⟩) (a := ⟨1⟩) (t := [⟨1⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (dup1_xstep (code := witnessEnv.code) (pcv := ⟨1074⟩) (a := ⟨0⟩) (t := [⟨1⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (iszero_xstep (code := witnessEnv.code) (pcv := ⟨1075⟩) (a := ⟨0⟩) (t := [⟨0⟩, ⟨1⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (swap1_xstep (code := witnessEnv.code) (pcv := ⟨1076⟩) (a := ⟨1⟩) (b := ⟨0⟩) (t := [⟨1⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (push2_xstep (code := witnessEnv.code) (pcv := ⟨1077⟩) (argv := ⟨1095⟩) (rest := [⟨0⟩, ⟨1⟩, ⟨1⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (jumpi_nt_xstep (code := witnessEnv.code) (pcv := ⟨1080⟩) (a := ⟨1095⟩) (t := [⟨1⟩, ⟨1⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (pop_xstep (code := witnessEnv.code) (pcv := ⟨1081⟩) (a := ⟨1⟩) (t := [⟨1⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (push1_xstep (code := witnessEnv.code) (pcv := ⟨1082⟩) (argv := ⟨1⟩) (rest := [⟨1⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (push1_xstep (code := witnessEnv.code) (pcv := ⟨1084⟩) (argv := ⟨1⟩) (rest := [⟨1⟩, ⟨1⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (push1_xstep (code := witnessEnv.code) (pcv := ⟨1086⟩) (argv := ⟨160⟩) (rest := [⟨1⟩, ⟨1⟩, ⟨1⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (shl_xstep (code := witnessEnv.code) (pcv := ⟨1088⟩) (a := ⟨160⟩) (b := ⟨1⟩) (t := [⟨1⟩, ⟨1⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (sub_xstep (code := witnessEnv.code) (pcv := ⟨1089⟩) (a := ⟨1461501637330902918203684832716283019655932542976⟩) (b := ⟨1⟩) (t := [⟨1⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (dup2_xstep (code := witnessEnv.code) (pcv := ⟨1090⟩) (a := ⟨1461501637330902918203684832716283019655932542975⟩) (b := ⟨1⟩) (t := [⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (and_xstep (code := witnessEnv.code) (pcv := ⟨1091⟩) (a := ⟨1⟩) (b := ⟨1461501637330902918203684832716283019655932542975⟩) (t := [⟨1⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (address_xstep (code := witnessEnv.code) (pcv := ⟨1092⟩) (rest := [⟨1⟩, ⟨1⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (eq_xstep (code := witnessEnv.code) (pcv := ⟨1093⟩) (a := ⟨42⟩) (b := ⟨1⟩) (t := [⟨1⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (iszero_xstep (code := witnessEnv.code) (pcv := ⟨1094⟩) (a := ⟨0⟩) (t := [⟨1⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (jumpdest_xstep (code := witnessEnv.code) (pcv := ⟨1095⟩)  rfl rfl (by decide +kernel) (by decide +kernel))
  deposit_witness_step (push2_xstep (code := witnessEnv.code) (pcv := ⟨1096⟩) (argv := ⟨1103⟩) (rest := [⟨1⟩, ⟨1⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (jumpi_t_xstep (code := witnessEnv.code) (pcv := ⟨1099⟩) (a := ⟨1103⟩) (b := ⟨1⟩) (t := [⟨1⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel) (jumpScan_valid witnessEnv.code 1103 1429 (by decide +kernel)) (by decide +kernel))
  deposit_witness_step (jumpdest_xstep (code := witnessEnv.code) (pcv := ⟨1103⟩)  rfl rfl (by decide +kernel) (by decide +kernel))
  deposit_witness_step (callvalue_xstep (code := witnessEnv.code) (pcv := ⟨1104⟩) (rest := [⟨1⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (push0_xstep (code := witnessEnv.code) (pcv := ⟨1105⟩) (rest := [⟨1⟩, ⟨1⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (sub_xstep (code := witnessEnv.code) (pcv := ⟨1106⟩) (a := ⟨0⟩) (b := ⟨1⟩) (t := [⟨1⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (push2_xstep (code := witnessEnv.code) (pcv := ⟨1107⟩) (argv := ⟨1114⟩) (rest := [⟨115792089237316195423570985008687907853269984665640564039457584007913129639935⟩, ⟨1⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (jumpi_t_xstep (code := witnessEnv.code) (pcv := ⟨1110⟩) (a := ⟨1114⟩) (b := ⟨115792089237316195423570985008687907853269984665640564039457584007913129639935⟩) (t := [⟨1⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel) (jumpScan_valid witnessEnv.code 1114 1429 (by decide +kernel)) (by decide +kernel))
  deposit_witness_step (jumpdest_xstep (code := witnessEnv.code) (pcv := ⟨1114⟩)  rfl rfl (by decide +kernel) (by decide +kernel))
  deposit_witness_step (push1_xstep (code := witnessEnv.code) (pcv := ⟨1115⟩) (argv := ⟨1⟩) (rest := [⟨1⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (push1_xstep (code := witnessEnv.code) (pcv := ⟨1117⟩) (argv := ⟨1⟩) (rest := [⟨1⟩, ⟨1⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (push1_xstep (code := witnessEnv.code) (pcv := ⟨1119⟩) (argv := ⟨160⟩) (rest := [⟨1⟩, ⟨1⟩, ⟨1⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (shl_xstep (code := witnessEnv.code) (pcv := ⟨1121⟩) (a := ⟨160⟩) (b := ⟨1⟩) (t := [⟨1⟩, ⟨1⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (sub_xstep (code := witnessEnv.code) (pcv := ⟨1122⟩) (a := ⟨1461501637330902918203684832716283019655932542976⟩) (b := ⟨1⟩) (t := [⟨1⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (dup2_xstep (code := witnessEnv.code) (pcv := ⟨1123⟩) (a := ⟨1461501637330902918203684832716283019655932542975⟩) (b := ⟨1⟩) (t := [⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (and_xstep (code := witnessEnv.code) (pcv := ⟨1124⟩) (a := ⟨1⟩) (b := ⟨1461501637330902918203684832716283019655932542975⟩) (t := [⟨1⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (push0_xstep (code := witnessEnv.code) (pcv := ⟨1125⟩) (rest := [⟨1⟩, ⟨1⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (swap1_xstep (code := witnessEnv.code) (pcv := ⟨1126⟩) (a := ⟨0⟩) (b := ⟨1⟩) (t := [⟨1⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (dup2_xstep (code := witnessEnv.code) (pcv := ⟨1127⟩) (a := ⟨1⟩) (b := ⟨0⟩) (t := [⟨1⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (mstore_xstep (code := witnessEnv.code) (pcv := ⟨1128⟩) (a := ⟨0⟩) (b := ⟨1⟩) (t := [⟨0⟩, ⟨1⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (push1_xstep (code := witnessEnv.code) (pcv := ⟨1129⟩) (argv := ⟨4⟩) (rest := [⟨0⟩, ⟨1⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (push1_xstep (code := witnessEnv.code) (pcv := ⟨1131⟩) (argv := ⟨32⟩) (rest := [⟨4⟩, ⟨0⟩, ⟨1⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (mstore_xstep (code := witnessEnv.code) (pcv := ⟨1133⟩) (a := ⟨32⟩) (b := ⟨4⟩) (t := [⟨0⟩, ⟨1⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (push1_xstep (code := witnessEnv.code) (pcv := ⟨1134⟩) (argv := ⟨64⟩) (rest := [⟨0⟩, ⟨1⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (dup2_xstep (code := witnessEnv.code) (pcv := ⟨1136⟩) (a := ⟨64⟩) (b := ⟨0⟩) (t := [⟨1⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (keccak_xstep (code := witnessEnv.code) (pcv := ⟨1137⟩) (a := ⟨0⟩) (b := ⟨64⟩) (t := [⟨0⟩, ⟨1⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  simp only [stKeccak]
  conv in Ethereum.KEC _ =>
    arg 1
    tactic => keccak_cbv
  conv in Ethereum.KEC _ =>
    tactic => exact witness_hash (by decide +kernel)
  deposit_witness_step (dup1_xstep (code := witnessEnv.code) (pcv := ⟨1138⟩) (a := ⟨77725202164364049732730867459915098663759625749236281158857587643401898360325⟩) (t := [⟨0⟩, ⟨1⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (sload_xstep (code := witnessEnv.code) (pcv := ⟨1139⟩) (a := ⟨77725202164364049732730867459915098663759625749236281158857587643401898360325⟩) (t := [⟨77725202164364049732730867459915098663759625749236281158857587643401898360325⟩, ⟨0⟩, ⟨1⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (callvalue_xstep (code := witnessEnv.code) (pcv := ⟨1140⟩) (rest := [⟨0⟩, ⟨77725202164364049732730867459915098663759625749236281158857587643401898360325⟩, ⟨0⟩, ⟨1⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (swap3_xstep (code := witnessEnv.code) (pcv := ⟨1141⟩) (a := ⟨1⟩) (b := ⟨0⟩) (c := ⟨77725202164364049732730867459915098663759625749236281158857587643401898360325⟩) (d := ⟨0⟩) (t := [⟨1⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (swap1_xstep (code := witnessEnv.code) (pcv := ⟨1142⟩) (a := ⟨0⟩) (b := ⟨0⟩) (t := [⟨77725202164364049732730867459915098663759625749236281158857587643401898360325⟩, ⟨1⟩, ⟨1⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (push2_xstep (code := witnessEnv.code) (pcv := ⟨1143⟩) (argv := ⟨1153⟩) (rest := [⟨0⟩, ⟨0⟩, ⟨77725202164364049732730867459915098663759625749236281158857587643401898360325⟩, ⟨1⟩, ⟨1⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (swap1_xstep (code := witnessEnv.code) (pcv := ⟨1146⟩) (a := ⟨1153⟩) (b := ⟨0⟩) (t := [⟨0⟩, ⟨77725202164364049732730867459915098663759625749236281158857587643401898360325⟩, ⟨1⟩, ⟨1⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (dup5_xstep (code := witnessEnv.code) (pcv := ⟨1147⟩) (a := ⟨0⟩) (b := ⟨1153⟩) (c := ⟨0⟩) (d := ⟨77725202164364049732730867459915098663759625749236281158857587643401898360325⟩) (e := ⟨1⟩) (t := [⟨1⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (swap1_xstep (code := witnessEnv.code) (pcv := ⟨1148⟩) (a := ⟨1⟩) (b := ⟨0⟩) (t := [⟨1153⟩, ⟨0⟩, ⟨77725202164364049732730867459915098663759625749236281158857587643401898360325⟩, ⟨1⟩, ⟨1⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (push2_xstep (code := witnessEnv.code) (pcv := ⟨1149⟩) (argv := ⟨1385⟩) (rest := [⟨0⟩, ⟨1⟩, ⟨1153⟩, ⟨0⟩, ⟨77725202164364049732730867459915098663759625749236281158857587643401898360325⟩, ⟨1⟩, ⟨1⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (jump_xstep (code := witnessEnv.code) (pcv := ⟨1152⟩) (a := ⟨1385⟩) (t := [⟨0⟩, ⟨1⟩, ⟨1153⟩, ⟨0⟩, ⟨77725202164364049732730867459915098663759625749236281158857587643401898360325⟩, ⟨1⟩, ⟨1⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (jumpScan_valid witnessEnv.code 1385 1429 (by decide +kernel)) (by decide +kernel))
  deposit_witness_step (jumpdest_xstep (code := witnessEnv.code) (pcv := ⟨1385⟩)  rfl rfl (by decide +kernel) (by decide +kernel))
  deposit_witness_step (dup1_xstep (code := witnessEnv.code) (pcv := ⟨1386⟩) (a := ⟨0⟩) (t := [⟨1⟩, ⟨1153⟩, ⟨0⟩, ⟨77725202164364049732730867459915098663759625749236281158857587643401898360325⟩, ⟨1⟩, ⟨1⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (dup3_xstep (code := witnessEnv.code) (pcv := ⟨1387⟩) (a := ⟨0⟩) (b := ⟨0⟩) (c := ⟨1⟩) (t := [⟨1153⟩, ⟨0⟩, ⟨77725202164364049732730867459915098663759625749236281158857587643401898360325⟩, ⟨1⟩, ⟨1⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (add_xstep (code := witnessEnv.code) (pcv := ⟨1388⟩) (a := ⟨1⟩) (b := ⟨0⟩) (t := [⟨0⟩, ⟨1⟩, ⟨1153⟩, ⟨0⟩, ⟨77725202164364049732730867459915098663759625749236281158857587643401898360325⟩, ⟨1⟩, ⟨1⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (dup1_xstep (code := witnessEnv.code) (pcv := ⟨1389⟩) (a := ⟨1⟩) (t := [⟨0⟩, ⟨1⟩, ⟨1153⟩, ⟨0⟩, ⟨77725202164364049732730867459915098663759625749236281158857587643401898360325⟩, ⟨1⟩, ⟨1⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (dup3_xstep (code := witnessEnv.code) (pcv := ⟨1390⟩) (a := ⟨1⟩) (b := ⟨1⟩) (c := ⟨0⟩) (t := [⟨1⟩, ⟨1153⟩, ⟨0⟩, ⟨77725202164364049732730867459915098663759625749236281158857587643401898360325⟩, ⟨1⟩, ⟨1⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (gt_xstep (code := witnessEnv.code) (pcv := ⟨1391⟩) (a := ⟨0⟩) (b := ⟨1⟩) (t := [⟨1⟩, ⟨0⟩, ⟨1⟩, ⟨1153⟩, ⟨0⟩, ⟨77725202164364049732730867459915098663759625749236281158857587643401898360325⟩, ⟨1⟩, ⟨1⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (iszero_xstep (code := witnessEnv.code) (pcv := ⟨1392⟩) (a := ⟨0⟩) (t := [⟨1⟩, ⟨0⟩, ⟨1⟩, ⟨1153⟩, ⟨0⟩, ⟨77725202164364049732730867459915098663759625749236281158857587643401898360325⟩, ⟨1⟩, ⟨1⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (push2_xstep (code := witnessEnv.code) (pcv := ⟨1393⟩) (argv := ⟨1404⟩) (rest := [⟨1⟩, ⟨1⟩, ⟨0⟩, ⟨1⟩, ⟨1153⟩, ⟨0⟩, ⟨77725202164364049732730867459915098663759625749236281158857587643401898360325⟩, ⟨1⟩, ⟨1⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (jumpi_t_xstep (code := witnessEnv.code) (pcv := ⟨1396⟩) (a := ⟨1404⟩) (b := ⟨1⟩) (t := [⟨1⟩, ⟨0⟩, ⟨1⟩, ⟨1153⟩, ⟨0⟩, ⟨77725202164364049732730867459915098663759625749236281158857587643401898360325⟩, ⟨1⟩, ⟨1⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel) (jumpScan_valid witnessEnv.code 1404 1429 (by decide +kernel)) (by decide +kernel))
  deposit_witness_step (jumpdest_xstep (code := witnessEnv.code) (pcv := ⟨1404⟩)  rfl rfl (by decide +kernel) (by decide +kernel))
  deposit_witness_step (swap3_xstep (code := witnessEnv.code) (pcv := ⟨1405⟩) (a := ⟨1⟩) (b := ⟨0⟩) (c := ⟨1⟩) (d := ⟨1153⟩) (t := [⟨0⟩, ⟨77725202164364049732730867459915098663759625749236281158857587643401898360325⟩, ⟨1⟩, ⟨1⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (swap2_xstep (code := witnessEnv.code) (pcv := ⟨1406⟩) (a := ⟨1153⟩) (b := ⟨0⟩) (c := ⟨1⟩) (t := [⟨1⟩, ⟨0⟩, ⟨77725202164364049732730867459915098663759625749236281158857587643401898360325⟩, ⟨1⟩, ⟨1⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (pop_xstep (code := witnessEnv.code) (pcv := ⟨1407⟩) (a := ⟨1⟩) (t := [⟨0⟩, ⟨1153⟩, ⟨1⟩, ⟨0⟩, ⟨77725202164364049732730867459915098663759625749236281158857587643401898360325⟩, ⟨1⟩, ⟨1⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (pop_xstep (code := witnessEnv.code) (pcv := ⟨1408⟩) (a := ⟨0⟩) (t := [⟨1153⟩, ⟨1⟩, ⟨0⟩, ⟨77725202164364049732730867459915098663759625749236281158857587643401898360325⟩, ⟨1⟩, ⟨1⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (jump_xstep (code := witnessEnv.code) (pcv := ⟨1409⟩) (a := ⟨1153⟩) (t := [⟨1⟩, ⟨0⟩, ⟨77725202164364049732730867459915098663759625749236281158857587643401898360325⟩, ⟨1⟩, ⟨1⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (jumpScan_valid witnessEnv.code 1153 1429 (by decide +kernel)) (by decide +kernel))
  deposit_witness_step (jumpdest_xstep (code := witnessEnv.code) (pcv := ⟨1153⟩)  rfl rfl (by decide +kernel) (by decide +kernel))
  deposit_witness_step (swap1_xstep (code := witnessEnv.code) (pcv := ⟨1154⟩) (a := ⟨1⟩) (b := ⟨0⟩) (t := [⟨77725202164364049732730867459915098663759625749236281158857587643401898360325⟩, ⟨1⟩, ⟨1⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (swap2_xstep (code := witnessEnv.code) (pcv := ⟨1155⟩) (a := ⟨0⟩) (b := ⟨1⟩) (c := ⟨77725202164364049732730867459915098663759625749236281158857587643401898360325⟩) (t := [⟨1⟩, ⟨1⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (sstore_xstep (code := witnessEnv.code) (pcv := ⟨1156⟩) (slot := ⟨77725202164364049732730867459915098663759625749236281158857587643401898360325⟩) (val := ⟨1⟩) (t := [⟨0⟩, ⟨1⟩, ⟨1⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) rfl (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (pop_xstep (code := witnessEnv.code) (pcv := ⟨1157⟩) (a := ⟨0⟩) (t := [⟨1⟩, ⟨1⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (pop_xstep (code := witnessEnv.code) (pcv := ⟨1158⟩) (a := ⟨1⟩) (t := [⟨1⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (push0_xstep (code := witnessEnv.code) (pcv := ⟨1159⟩) (rest := [⟨1⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (push1_xstep (code := witnessEnv.code) (pcv := ⟨1160⟩) (argv := ⟨6⟩) (rest := [⟨0⟩, ⟨1⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (sstore_xstep (code := witnessEnv.code) (pcv := ⟨1162⟩) (slot := ⟨6⟩) (val := ⟨0⟩) (t := [⟨1⟩, ⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) rfl (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (pop_xstep (code := witnessEnv.code) (pcv := ⟨1163⟩) (a := ⟨1⟩) (t := [⟨226⟩, ⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel))
  deposit_witness_step (jump_xstep (code := witnessEnv.code) (pcv := ⟨1164⟩) (a := ⟨226⟩) (t := [⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (jumpScan_valid witnessEnv.code 226 1429 (by decide +kernel)) (by decide +kernel))
  deposit_witness_step (jumpdest_xstep (code := witnessEnv.code) (pcv := ⟨226⟩)  rfl rfl (by decide +kernel) (by decide +kernel))
  apply execution_return
  · rw [stop_xstep (code := witnessEnv.code) (pcv := ⟨227⟩) (stk := [⟨4081121793⟩]) rfl rfl (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel)]
  · rfl
end DepositWitness
end Rollup.EVM
