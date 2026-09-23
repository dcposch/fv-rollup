import invariants.Obligations
import proofs.SourceSteps
import proofs.SolmGuards
import proofs.Storage
import proofs.PackedAddress
import Reasoning.Storage

open Solm ABI Ethereum Reasoning.Theory

namespace Rollup.EVM

def constructorLocals (sequencer : Address) (root : Root) : Store :=
  ((∅ : Store).insert "initialRoot" (rootValue root)).insert "sequencer_" (.address sequencer)

def constructorState (evm : Ethereum.State) (sequencer : Address) (root : Root) : Ethereum.State :=
  Solm.EVM.storageStore
    (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩ (UInt256.ofNat sequencer.val))
    evm.executionEnv.codeOwner ⟨1⟩ ⟨root⟩

theorem rootValue_word (root : Root) : valueToWord (rootValue root) = some ⟨root⟩ := by
  have len : (_root_.EVM.Word.toBytesBE (⟨root⟩ : UInt256)).length = 32 := by
    simpa using word_toBytesBE_toByteArray_size (⟨root⟩ : UInt256)
  have h := congrArg some (keyValueToWord_fixedBytes32 (⟨root⟩ : UInt256))
  simpa [rootValue, toByteArray_eq_toBytesBE, byteArray_toList_eq, valueToWord, keyValueToWord, len] using h

theorem constructor_seq_guard_get (evm : Ethereum.State) (sequencer : Address) (locals : Store)
    (getSeq : locals.get? "sequencer_" = some (.address sequencer)) :
    evalExpr? config ⟨contract, locals⟩ evm
      (.binary .ne (.var "sequencer_") (.cast (.intLit 0) (.elem .address))) =
      .ok (.bool (sequencer != 0)) := by
  simp only [evalExpr?, getSeq, EvalResult.ofOption, EvalResult.bind,
    bind, pure, castValue?, evalBinaryOp?]
  by_cases h : sequencer = 0
  · subst sequencer; rfl
  · have ne : (Value.address sequencer == Value.address (AccountAddress.ofNat 0)) = false := by
      apply beq_eq_false_iff_ne.mpr
      simpa using h
    simp [ne, h]

theorem constructor_seq_guard (evm : Ethereum.State) (sequencer : Address) (root : Root) :
    evalExpr? config ⟨contract, constructorLocals sequencer root⟩ evm
      (.binary .ne (.var "sequencer_") (.cast (.intLit 0) (.elem .address))) =
      .ok (.bool (sequencer != 0)) :=
  constructor_seq_guard_get evm sequencer _ (by simp [constructorLocals])

def constructorPackedState (evm : Ethereum.State) (sequencer : Address) (root : Root) : Ethereum.State :=
  Solm.EVM.storageStore
    (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩
      (packedAddress (readWord evm evm.executionEnv.codeOwner ⟨0⟩) (UInt256.ofNat sequencer.val)))
    evm.executionEnv.codeOwner ⟨1⟩ ⟨root⟩

/-- Execute the constructor with either parameter-store representation. -/
theorem constructor_source_packed (evm : Ethereum.State) (sequencer : Address) (root : Root)
    (locals : Store)
    (getSeq : locals.get? "sequencer_" = some (.address sequencer))
    (getRoot : locals.get? "initialRoot" = some (rootValue root))
    (noSeq : locals.get? "sequencer" = none)
    (noRoot : locals.get? "stateRoot" = none)
    (nonzero : sequencer ≠ 0) (nonpayable : evm.executionEnv.weiValue = ⟨0⟩) :
    ExactBlock config ⟨contract, locals⟩ evm contract.ctor.body
      (.ok ⟨contract, locals⟩ (constructorPackedState evm sequencer root)) := by
  let first := Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩
    (packedAddress (readWord evm evm.executionEnv.codeOwner ⟨0⟩) (UInt256.ofNat sequencer.val))
  have canonical : (UInt256.ofNat sequencer.val).toNat < _root_.EVM.addressModulus := by
    simp [UInt256.ofNat, UInt256.toNat, Id.run, _root_.EVM.addressModulus, _root_.EVM.twoPow,
      Nat.mod_eq_of_lt (lt_trans sequencer.isLt (by decide : 2 ^ 160 < UInt256.size))]
  have address_eq : AccountAddress.ofNat (UInt256.ofNat sequencer.val).toNat = sequencer := by
    apply Fin.ext
    simp [AccountAddress.ofNat, AccountAddress.size, UInt256.ofNat, UInt256.toNat, Id.run,
      Nat.mod_eq_of_lt (lt_trans sequencer.isLt (by decide : 2 ^ 160 < UInt256.size))]
  have seqStore : storageLocStore evm (addressOffset0Loc ⟨0⟩) (.address sequencer) = some first := by
    have stored :=  store_address_packed evm ⟨0⟩ (UInt256.ofNat sequencer.val) canonical
    rw [address_eq] at stored
    exact stored
  have seqAssign : assignStorageRef? config ⟨contract, locals⟩
      evm .storage ⟨"sequencer", []⟩ (.address sequencer) =
      .ok (⟨contract, locals⟩, first) := by
    apply assignStorageRef_storage_scalar_value (er := ⟨"sequencer", []⟩)
      (loc := addressOffset0Loc ⟨0⟩)
    · exact noSeq
    · simp [evalStorageRef, evalStorageRefSteps, EvalResult.bind, bind, pure]
    · rfl
    · rfl
    · trivial
    · exact seqStore
  have rootAssign : assignStorageRef? config ⟨contract, locals⟩
      first .storage ⟨"stateRoot", []⟩ (rootValue root) =
      .ok (⟨contract, locals⟩, constructorPackedState evm sequencer root) := by
    apply assignStorageRef_storage_scalar_value (er := ⟨"stateRoot", []⟩)
      (loc := bytes32Loc ⟨1⟩)
    · exact noRoot
    · simp [evalStorageRef, evalStorageRefSteps, EvalResult.bind, bind, pure]
    · rfl
    · rfl
    · trivial
    · simpa [constructorPackedState, first, storageStore_executionEnv] using
        storageLocStore_bytes32 first ⟨1⟩ ⟨root⟩ (rootValue root) (rootValue_word root)
  apply exact_cons (exact_require_true (evalCallvalueEq_true nonpayable))
  refine exact_cons (exact_require_true ?_) ?_
  · rw [constructor_seq_guard_get evm sequencer locals getSeq]
    simp [nonzero]
  refine exact_cons (exact_assign (value := .address sequencer) ?_ seqAssign) ?_
  · simp only [evalExpr?, getSeq, EvalResult.ofOption]
  refine exact_cons (exact_assign (value := rootValue root) ?_ rootAssign) ?_
  · simp only [evalExpr?, getRoot, EvalResult.ofOption]
  exact exact_nil _ _ _

/-- Execute both constructor writes. ETH already at the address stays there. -/
theorem constructor_source_exact (evm : Ethereum.State) (sequencer : Address) (root : Root)
    (nonzero : sequencer ≠ 0) (nonpayable : evm.executionEnv.weiValue = ⟨0⟩)
    (fresh : readWord evm evm.executionEnv.codeOwner ⟨0⟩ = ⟨0⟩) :
    ExactBlock config ⟨contract, constructorLocals sequencer root⟩ evm contract.ctor.body
      (.ok ⟨contract, constructorLocals sequencer root⟩ (constructorState evm sequencer root)) := by
  have canonical : (UInt256.ofNat sequencer.val).toNat < _root_.EVM.addressModulus := by
    simp [UInt256.ofNat, UInt256.toNat, Id.run, _root_.EVM.addressModulus, _root_.EVM.twoPow,
      Nat.mod_eq_of_lt (lt_trans sequencer.isLt (by decide : 2 ^ 160 < UInt256.size))]
  have execution := constructor_source_packed evm sequencer root (constructorLocals sequencer root)
    (by simp [constructorLocals])
    (by unfold constructorLocals
        rw [store_get_ne _ _ (by decide)]
        exact store_get_self _ _ _)
    (by simp [constructorLocals]) (by simp [constructorLocals]) nonzero nonpayable
  simpa only [constructorPackedState, fresh, packedAddress_zero _ canonical, constructorState] using execution

theorem constructor_storage (evm : Ethereum.State) (sequencer : Address) (root : Root)
    {acc : Account} (present : evm.lookupAccount evm.executionEnv.codeOwner = some acc)
    (slot : UInt256) :
    readWord (constructorState evm sequencer root) evm.executionEnv.codeOwner slot =
      if slot = ⟨1⟩ then ⟨root⟩ else
      if slot = ⟨0⟩ then UInt256.ofNat sequencer.val else
      readWord evm evm.executionEnv.codeOwner slot := by
  let first := Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩
    (UInt256.ofNat sequencer.val)
  have firstPresent : first.lookupAccount evm.executionEnv.codeOwner =
      some (acc.updateStorage ⟨0⟩ (UInt256.ofNat sequencer.val)) := by
    simp [first, lookup_store_self, present]
  change Solm.EVM.storageLoad (Solm.EVM.storageStore first _ ⟨1⟩ ⟨root⟩) _ _ = _
  by_cases one : slot = ⟨1⟩
  · subst slot
    simp only [↓reduceIte]
    exact storageLoad_storageStore_same_present first _ firstPresent _ _
  · rw [storageLoad_storageStore_ne _ _ one]
    by_cases zero : slot = ⟨0⟩
    · subst slot
      simp only [one, ↓reduceIte]
      exact storageLoad_storageStore_same_present evm _ present _ _
    · simp only [one, zero, ↓reduceIte]
      exact storageLoad_storageStore_ne evm _ zero

theorem constructor_balance (evm : Ethereum.State) (sequencer : Address) (root : Root) :
    ((constructorState evm sequencer root).lookupAccount evm.executionEnv.codeOwner).map (·.balance) =
      (evm.lookupAccount evm.executionEnv.codeOwner).map (·.balance) := by
  simp only [constructorState, balance_store]

theorem constructor_projection (evm : Ethereum.State) (sequencer : Address) (root : Root)
    {acc : Account} (present : evm.lookupAccount evm.executionEnv.codeOwner = some acc)
    (fresh : ∀ slot, readWord evm evm.executionEnv.codeOwner slot = ⟨0⟩) :
    project (constructorState evm sequencer root) evm.executionEnv.codeOwner fixedKeys =
      initial evm.executionEnv.codeOwner sequencer root
        (project evm evm.executionEnv.codeOwner fixedKeys).eth := by
  have balance := constructor_balance evm sequencer root
  have eth : (((constructorState evm sequencer root).lookupAccount evm.executionEnv.codeOwner).elim
      (⟨0⟩ : UInt256) (·.balance)).toNat =
      ((evm.lookupAccount evm.executionEnv.codeOwner).elim (⟨0⟩ : UInt256) (·.balance)).toNat := by
    cases hout : (constructorState evm sequencer root).lookupAccount evm.executionEnv.codeOwner <;>
      simp_all
  have address : AccountAddress.ofUInt256 (UInt256.ofNat sequencer.val) = sequencer := by
    apply Fin.ext
    simp [AccountAddress.ofUInt256, AccountAddress.size,
      UInt256.ofNat, Id.run,
      Nat.mod_eq_of_lt (lt_trans sequencer.isLt (by decide : 2 ^ 160 < UInt256.size))]
  have hp : pendingLedger (constructorState evm sequencer root) evm.executionEnv.codeOwner fixedKeys =
      fun _ => 0 := by
    funext a
    simp [pendingLedger, fixedKeys]
  have hc : claimLedger (constructorState evm sequencer root) evm.executionEnv.codeOwner fixedKeys =
      fun _ => 0 := by
    funext a
    simp [claimLedger, fixedKeys]
  simp only [project, initial, constructor_storage evm sequencer root present, fresh, hp, hc, eth]
  simp [UInt256.size, address, UInt256.toNat]

theorem constructor_storage_ready (evm : Ethereum.State) (sequencer : Address) (root : Root)
    {acc : Account} (present : evm.lookupAccount evm.executionEnv.codeOwner = some acc)
    (fresh : ∀ slot, readWord evm evm.executionEnv.codeOwner slot = ⟨0⟩) :
    StorageReady (constructorState evm sequencer root) evm.executionEnv.codeOwner fixedKeys := by
  refine ⟨Finset.Subset.refl _, noAlias_fixed, ?_⟩
  intro slot outside
  have zero := outside (.fixed 0) (by simp [fixedKeys])
  have one := outside (.fixed 1) (by simp [fixedKeys])
  change (⟨0⟩ : UInt256) ≠ slot at zero
  change (⟨1⟩ : UInt256) ≠ slot at one
  rw [constructor_storage evm sequencer root present slot]
  simp [Ne.symm one, Ne.symm zero, fresh]

theorem constructor_initializes : ConstructorInitializes := by
  intro evm out locals frame sequencer root args present fresh run
  change some (constructorLocals sequencer root) = some locals at args
  have localEq := Option.some.inj args
  subst locals
  have nonpayable : evm.executionEnv.weiValue = ⟨0⟩ := by
    by_contra nonzero
    have impossible := func_only_reverts
      (fun _ h => require_false_only_reverts (evalCallvalueEq_false nonzero) h) run
    cases impossible
  have nonzero : sequencer ≠ 0 := by
    intro zero
    subst sequencer
    have guard := constructor_seq_guard evm 0 root
    simp only [bne_self_eq_false] at guard
    have impossible := func_only_reverts
      (fun _ h => second_guard_only_reverts guard h) run
    cases impossible
  have exactRun := exact_function (constructor_source_exact evm sequencer root nonzero nonpayable (fresh ⟨0⟩))
  have output := exactRun.2 _ run
  have outEq := (ExecResult.returned.inj output).2.1
  subst out
  obtain ⟨acc, account⟩ := Option.isSome_iff_exists.mp present
  refine ⟨nonzero, constructor_projection evm sequencer root account fresh,
    constructor_storage_ready evm sequencer root account fresh, ?_, ?_⟩
  · rw [constructor_storage evm sequencer root account ⟨6⟩]
    simpa using fresh ⟨6⟩
  · simp only [constructorState, storageStore_executionEnv]

end Rollup.EVM
