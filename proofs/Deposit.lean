import semantics.Bindings
import proofs.SourceSteps
import proofs.SourceStorage
import proofs.Storage

open Solm ABI Ethereum Reasoning.Theory

namespace Rollup.EVM

def depositLocals (owner : Address) : Store := (∅ : Store).insert "owner" (.address owner)

def nextDepositCredit (evm : Ethereum.State) (owner : Address) : Nat :=
  (readWord evm evm.executionEnv.codeOwner (keySlot (.pending owner))).toNat +
    evm.executionEnv.weiValue.toNat

def depositState (evm : Ethereum.State) (owner : Address) : Ethereum.State :=
  let locked := Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨6⟩ ⟨1⟩
  let credited := Solm.EVM.storageStore locked evm.executionEnv.codeOwner
    (keySlot (.pending owner)) (UInt256.ofNat (nextDepositCredit evm owner))
  Solm.EVM.storageStore credited evm.executionEnv.codeOwner ⟨6⟩ ⟨0⟩

/-- Read credit after the lock write, including possible slot aliases. -/
def depositExecutionCredit (evm : Ethereum.State) (owner : Address) : Nat :=
  (readWord (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨6⟩ ⟨1⟩)
    evm.executionEnv.codeOwner (keySlot (.pending owner))).toNat +
      evm.executionEnv.weiValue.toNat

def depositExecutionState (evm : Ethereum.State) (owner : Address) : Ethereum.State :=
  let locked := Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨6⟩ ⟨1⟩
  let credited := Solm.EVM.storageStore locked evm.executionEnv.codeOwner
    (keySlot (.pending owner)) (UInt256.ofNat (depositExecutionCredit evm owner))
  Solm.EVM.storageStore credited evm.executionEnv.codeOwner ⟨6⟩ ⟨0⟩

/-- Execute the deposit body and determine its unique source result. -/
theorem deposit_body_exact (evm : Ethereum.State) (owner : Address)
    (unlocked : readWord evm evm.executionEnv.codeOwner ⟨6⟩ = ⟨0⟩)
    (nonzeroOwner : owner ≠ 0) (notSelf : owner ≠ evm.executionEnv.codeOwner)
    (nonzeroValue : evm.executionEnv.weiValue ≠ ⟨0⟩)
    (bounded : depositExecutionCredit evm owner < wordLimit) :
    ExactBlock config ⟨contract, depositLocals owner⟩ evm contract.transitions[0]!.body
      (.ok ⟨contract, (depositLocals owner).insert "nextCredit" (.int (depositExecutionCredit evm owner))⟩
        (depositExecutionState evm owner)) := by
  let locals := depositLocals owner
  let next := depositExecutionCredit evm owner
  let extended := locals.insert "nextCredit" (.int next)
  let locked := Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨6⟩ ⟨1⟩
  let credited := Solm.EVM.storageStore locked evm.executionEnv.codeOwner
    (keySlot (.pending owner)) (UInt256.ofNat next)
  have lockedEnv : locked.executionEnv = evm.executionEnv := storageStore_executionEnv ..
  have creditedEnv : credited.executionEnv = evm.executionEnv := by
    simp only [credited, storageStore_executionEnv, lockedEnv]
  have arg : locals.get? "owner" = some (.address owner) := store_get_self _ _ _
  have extendedArg : extended.get? "owner" = some (.address owner) := by
    rw [store_get_ne _ _ (by decide)]
    exact arg
  have freeLock : locals.get? "entered" = none := by simp [locals, depositLocals]
  have freePending : locals.get? "pendingDeposits" = none := by simp [locals, depositLocals]
  have freeLock' : extended.get? "entered" = none := by simp [extended, locals, depositLocals]
  have freePending' : extended.get? "pendingDeposits" = none := by simp [extended, locals, depositLocals]
  have lockEval := eval_entered evm locals freeLock
  rw [unlocked] at lockEval
  have guard : evalExpr? config ⟨contract, locals⟩ evm
      (.binary .eq (.storage ⟨"entered", []⟩) (.intLit 0)) = .ok (.bool true) := by
    simp only [evalExpr?, lockEval, bind, EvalResult.bind, pure, evalBinaryOp?]
    rfl
  have ownerZero : (Value.address owner == Value.address (AccountAddress.ofNat 0)) = false := by
    apply beq_eq_false_iff_ne.mpr
    simpa using nonzeroOwner
  have ownerSelf : (Value.address owner == Value.address evm.executionEnv.codeOwner) = false := by
    apply beq_eq_false_iff_ne.mpr
    simpa using notSelf
  have ownerGuard : evalExpr? config ⟨contract, locals⟩ locked
      (.binary .and
        (.binary .ne (.var "owner") (.cast (.intLit 0) (.elem .address)))
        (.binary .ne (.var "owner") (.env .this))) = .ok (.bool true) := by
    simp only [evalExpr?, arg, EvalResult.ofOption, EvalResult.bind, bind, pure,
      evalBinaryOp?, castValue?, envValue, lockedEnv, Int.lt_irrefl, ↓reduceIte, Int.toNat_zero]
    simp [ownerZero, ownerSelf]
  have valueNe : (Value.int (Int.ofNat evm.executionEnv.weiValue.toNat) == Value.int 0) = false := by
    apply beq_eq_false_iff_ne.mpr
    intro equal
    exact nonzeroValue (uint256_toNat_eq_zero (Int.ofNat.inj (Value.int.inj equal)))
  have valueGuard : evalExpr? config ⟨contract, locals⟩ locked
      (.binary .ne (.env .callvalue) (.intLit 0)) = .ok (.bool true) := by
    simp only [evalExpr?, EvalResult.bind, bind, pure, envValue, lockedEnv, evalBinaryOp?]
    change EvalResult.ok (Value.bool (!(Value.int (Int.ofNat evm.executionEnv.weiValue.toNat) == .int 0))) = _
    rw [valueNe]
    rfl
  have creditLoad := eval_pending locked locals owner freePending arg
  rw [lockedEnv] at creditLoad
  have nextEval : evalExpr? config ⟨contract, locals⟩ locked
      (.binary .add (.storage ⟨"pendingDeposits", [.mindex (.var "owner")]⟩) (.env .callvalue)) =
      .ok (.int next) := by
    simp [evalExpr?, creditLoad, EvalResult.bind, bind, pure, envValue,
      lockedEnv, evalBinaryOp?, next, depositExecutionCredit]
    rfl
  have rangeGuard : evalExpr? config ⟨contract, extended⟩ locked
      (.binary .lt (.var "nextCredit") (.intLit (2 ^ 256))) = .ok (.bool true) := by
    have boundInt : (next : Int) < 2 ^ 256 := by exact_mod_cast bounded
    simp only [evalExpr?, extended, store_get_self, EvalResult.ofOption, EvalResult.bind,
      bind, pure, evalBinaryOp?, decide_eq_true boundInt]
  have nextWord : (UInt256.ofNat next).toNat = next := ulit_toNat' next bounded
  have storeCredit := assign_pending locked extended owner (UInt256.ofNat next) freePending' extendedArg
  rw [nextWord, lockedEnv] at storeCredit
  have unlock := assign_entered credited extended ⟨0⟩ freeLock'
  rw [creditedEnv] at unlock
  refine exact_cons (exact_require_true guard) ?_
  refine exact_cons (exact_assign (value := .int 1) ?_ (assign_entered evm locals ⟨1⟩ freeLock)) ?_
  · simp only [evalExpr?, pure]
  refine exact_cons (exact_require_true ownerGuard) ?_
  refine exact_cons (exact_require_true valueGuard) ?_
  refine exact_cons (exact_let nextEval) ?_
  refine exact_cons (exact_require_true rangeGuard) ?_
  refine exact_cons (exact_assign (value := .int next) ?_ storeCredit) ?_
  · simp only [evalExpr?, store_get_self, EvalResult.ofOption]
  refine exact_cons (exact_assign (value := .int 0) ?_ unlock) ?_
  · simp only [evalExpr?, pure]
  exact exact_nil _ _ _

/-- Distinct slots connect the execution credit to the model credit. -/
theorem deposit_execution_credit (evm : Ethereum.State) (owner : Address)
    (separate : keySlot (.pending owner) ≠ ⟨6⟩) :
    depositExecutionCredit evm owner = nextDepositCredit evm owner := by
  unfold depositExecutionCredit nextDepositCredit readWord
  rw [storageLoad_storageStore_ne evm _ separate]

/-- Execute the source deposit under the model's slot condition. -/
theorem deposit_source_exact (evm : Ethereum.State) (owner : Address)
    (unlocked : readWord evm evm.executionEnv.codeOwner ⟨6⟩ = ⟨0⟩)
    (nonzeroOwner : owner ≠ 0) (notSelf : owner ≠ evm.executionEnv.codeOwner)
    (nonzeroValue : evm.executionEnv.weiValue ≠ ⟨0⟩)
    (separate : keySlot (.pending owner) ≠ ⟨6⟩)
    (bounded : nextDepositCredit evm owner < wordLimit) :
    ExactBlock config ⟨contract, depositLocals owner⟩ evm contract.transitions[0]!.body
      (.ok ⟨contract, (depositLocals owner).insert "nextCredit" (.int (nextDepositCredit evm owner))⟩
        (depositState evm owner)) := by
  have credit := deposit_execution_credit evm owner separate
  simpa only [depositExecutionState, credit, depositState] using
    deposit_body_exact evm owner unlocked nonzeroOwner notSelf nonzeroValue
      (by simpa only [credit] using bounded)

theorem deposit_storage (evm : Ethereum.State) (owner : Address) (keys : AccessScope)
    {acc : Account} (present : evm.lookupAccount evm.executionEnv.codeOwner = some acc)
    (ready : StorageReady evm evm.executionEnv.codeOwner keys)
    (ownerKey : StorageKey.pending owner ∈ keys)
    (unlocked : readWord evm evm.executionEnv.codeOwner ⟨6⟩ = ⟨0⟩)
    (key : StorageKey) (tracked : key ∈ keys) :
    readWord (depositState evm owner) evm.executionEnv.codeOwner (keySlot key) =
      if key = .pending owner then UInt256.ofNat (nextDepositCredit evm owner)
      else readWord evm evm.executionEnv.codeOwner (keySlot key) := by
  let locked := Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨6⟩ ⟨1⟩
  let word := UInt256.ofNat (nextDepositCredit evm owner)
  let credited := Solm.EVM.storageStore locked evm.executionEnv.codeOwner (keySlot (.pending owner)) word
  have lockKey : StorageKey.fixed 6 ∈ keys := ready.1 (by simp [fixedKeys])
  have lockedPresent : locked.lookupAccount evm.executionEnv.codeOwner =
      some (acc.updateStorage ⟨6⟩ ⟨1⟩) := by simp [locked, lookup_store_self, present]
  have creditedPresent : credited.lookupAccount evm.executionEnv.codeOwner =
      some ((acc.updateStorage ⟨6⟩ ⟨1⟩).updateStorage (keySlot (.pending owner)) word) := by
    simp [credited, lookup_store_self, lockedPresent]
  change readWord (Solm.EVM.storageStore credited evm.executionEnv.codeOwner
    (keySlot (.fixed 6)) ⟨0⟩) evm.executionEnv.codeOwner (keySlot key) = _
  rw [read_store_key creditedPresent ready.2.1 tracked lockKey]
  change (if key = .fixed 6 then _ else
    readWord (Solm.EVM.storageStore locked evm.executionEnv.codeOwner (keySlot (.pending owner)) word)
      evm.executionEnv.codeOwner (keySlot key)) = _
  rw [read_store_key lockedPresent ready.2.1 tracked ownerKey]
  change (if key = .fixed 6 then _ else if key = .pending owner then _ else
    readWord (Solm.EVM.storageStore evm evm.executionEnv.codeOwner (keySlot (.fixed 6)) ⟨1⟩)
      evm.executionEnv.codeOwner (keySlot key)) = _
  rw [read_store_key present ready.2.1 tracked lockKey]
  by_cases isLock : key = .fixed 6
  · subst key
    simpa using unlocked.symm
  · simp only [isLock, ↓reduceIte]
    rfl

theorem deposit_balance (evm : Ethereum.State) (owner : Address) :
    ((depositState evm owner).lookupAccount evm.executionEnv.codeOwner).map (·.balance) =
      (evm.lookupAccount evm.executionEnv.codeOwner).map (·.balance) := by
  simp only [depositState, balance_store]

/-- Project the three storage writes to one logical deposit credit. -/
theorem deposit_projection (evm : Ethereum.State) (owner : Address) (keys : AccessScope)
    {acc : Account} (present : evm.lookupAccount evm.executionEnv.codeOwner = some acc)
    (ready : StorageReady evm evm.executionEnv.codeOwner keys)
    (ownerKey : StorageKey.pending owner ∈ keys)
    (unlocked : readWord evm evm.executionEnv.codeOwner ⟨6⟩ = ⟨0⟩)
    (bounded : nextDepositCredit evm owner < wordLimit)
    (funds : evm.executionEnv.weiValue.toNat ≤ (project evm evm.executionEnv.codeOwner keys).eth) :
    project (depositState evm owner) evm.executionEnv.codeOwner keys =
      deposit (beforeCall evm keys) owner evm.executionEnv.weiValue.toNat := by
  have slots := deposit_storage evm owner keys present ready ownerKey unlocked
  have fixed (i : Fin 7) : readWord (depositState evm owner) evm.executionEnv.codeOwner
      (keySlot (.fixed i)) = readWord evm evm.executionEnv.codeOwner (keySlot (.fixed i)) := by
    simpa using slots (.fixed i) (ready.1 (by simp [fixedKeys]))
  have pending : pendingLedger (depositState evm owner) evm.executionEnv.codeOwner keys =
      credit (pendingLedger evm evm.executionEnv.codeOwner keys) owner evm.executionEnv.weiValue.toNat := by
    funext a
    by_cases eqOwner : a = owner
    · subst a
      have update := slots (.pending owner) ownerKey
      simp only [↓reduceIte] at update
      simp only [pendingLedger, ownerKey, ↓reduceIte, credit, Function.update_self, update]
      rw [ulit_toNat' _ bounded]
      rfl
    · by_cases member : StorageKey.pending a ∈ keys
      · have update := slots (.pending a) member
        simp only [StorageKey.pending.injEq, eqOwner, ↓reduceIte] at update
        simp [pendingLedger, member, credit, eqOwner, update]
      · simp [pendingLedger, member, credit, eqOwner]
  have claims : claimLedger (depositState evm owner) evm.executionEnv.codeOwner keys =
      claimLedger evm evm.executionEnv.codeOwner keys := by
    funext a
    by_cases member : StorageKey.claims a ∈ keys
    · have update := slots (.claims a) member
      simp only [reduceCtorEq, ↓reduceIte] at update
      simp [claimLedger, member, update]
    · simp [claimLedger, member]
  have balance := deposit_balance evm owner
  have eth : (project (depositState evm owner) evm.executionEnv.codeOwner keys).eth =
      (project evm evm.executionEnv.codeOwner keys).eth := by
    cases hout : (depositState evm owner).lookupAccount evm.executionEnv.codeOwner <;>
      simp_all [project]
  have ethBefore : (project (depositState evm owner) evm.executionEnv.codeOwner keys).eth =
      (beforeCall evm keys).eth + evm.executionEnv.weiValue.toNat := by
    simpa only [beforeCall] using eth.trans (Nat.sub_add_cancel funds).symm
  have h0 := fixed 0
  have h1 := fixed 1
  have h2 := fixed 2
  have h3 := fixed 3
  change readWord (depositState evm owner) evm.executionEnv.codeOwner ⟨0⟩ =
    readWord evm evm.executionEnv.codeOwner ⟨0⟩ at h0
  change readWord (depositState evm owner) evm.executionEnv.codeOwner ⟨1⟩ =
    readWord evm evm.executionEnv.codeOwner ⟨1⟩ at h1
  change readWord (depositState evm owner) evm.executionEnv.codeOwner ⟨2⟩ =
    readWord evm evm.executionEnv.codeOwner ⟨2⟩ at h2
  change readWord (depositState evm owner) evm.executionEnv.codeOwner ⟨3⟩ =
    readWord evm evm.executionEnv.codeOwner ⟨3⟩ at h3
  simp only [project, beforeCall, deposit, h0, h1, h2, h3, pending, claims]
  congr 1

theorem deposit_storage_ready (evm : Ethereum.State) (owner : Address) (keys : AccessScope)
    (ready : StorageReady evm evm.executionEnv.codeOwner keys)
    (ownerKey : StorageKey.pending owner ∈ keys) :
    StorageReady (depositState evm owner) evm.executionEnv.codeOwner keys := by
  have lockKey : StorageKey.fixed 6 ∈ keys := ready.1 (by simp [fixedKeys])
  exact ⟨ready.1, ready.2.1,
    sparse_store (sparse_store (sparse_store ready.2.2 lockKey ⟨1⟩) ownerKey
      (UInt256.ofNat (nextDepositCredit evm owner))) lockKey ⟨0⟩⟩

theorem deposit_enabled (evm : Ethereum.State) (owner : Address) (keys : AccessScope)
    (ownerKey : StorageKey.pending owner ∈ keys)
    (nonzeroOwner : owner ≠ 0) (notSelf : owner ≠ evm.executionEnv.codeOwner)
    (nonzeroValue : evm.executionEnv.weiValue ≠ ⟨0⟩)
    (bounded : nextDepositCredit evm owner < wordLimit)
    (funds : evm.executionEnv.weiValue.toNat ≤ (project evm evm.executionEnv.codeOwner keys).eth) :
    DepositEnabled (beforeCall evm keys) owner evm.executionEnv.weiValue.toNat := by
  refine ⟨rfl, ⟨nonzeroOwner, notSelf⟩, ?_, ?_, ?_⟩
  · exact Nat.pos_of_ne_zero (fun h => nonzeroValue (uint256_toNat_eq_zero h))
  · simpa only [beforeCall, project, pendingLedger, ownerKey, ↓reduceIte, nextDepositCredit] using bounded
  · change (project evm evm.executionEnv.codeOwner keys).eth - evm.executionEnv.weiValue.toNat +
      evm.executionEnv.weiValue.toNat < wordLimit
    rw [Nat.sub_add_cancel funds]
    unfold project
    cases h : evm.lookupAccount evm.executionEnv.codeOwner with
    | none => change (0 : Nat) < wordLimit; decide
    | some acc => exact acc.balance.val.isLt

/-- A valid deposit has a source execution with exactly the labeled ledger effect. -/
theorem deposit_source_success (evm : Ethereum.State) (owner : Address) (keys : AccessScope)
    {acc : Account} (present : evm.lookupAccount evm.executionEnv.codeOwner = some acc)
    (ready : StorageReady evm evm.executionEnv.codeOwner keys)
    (ownerKey : StorageKey.pending owner ∈ keys)
    (unlocked : readWord evm evm.executionEnv.codeOwner ⟨6⟩ = ⟨0⟩)
    (nonzeroOwner : owner ≠ 0) (notSelf : owner ≠ evm.executionEnv.codeOwner)
    (nonzeroValue : evm.executionEnv.weiValue ≠ ⟨0⟩)
    (bounded : nextDepositCredit evm owner < wordLimit)
    (funds : evm.executionEnv.weiValue.toNat ≤ (project evm evm.executionEnv.codeOwner keys).eth) :
    ∃ frame,
      ExecTransitionBody config contract evm (depositLocals owner) contract.transitions[0]!.body
        (.returned frame (depositState evm owner) none) ∧
      CallStep (beforeCall evm keys)
        ⟨evm.executionEnv.source, evm.executionEnv.weiValue.toNat, .deposit owner⟩ (.success .unit) []
        (project (depositState evm owner) evm.executionEnv.codeOwner keys) ∧
      StorageReady (depositState evm owner) evm.executionEnv.codeOwner keys := by
  have separate : keySlot (.pending owner) ≠ ⟨6⟩ := by
    intro same
    have bad := ready.2.1 (.pending owner) ownerKey (.fixed 6)
      (ready.1 (by simp [fixedKeys])) same
    cases bad
  refine ⟨_, (exact_function (deposit_source_exact evm owner unlocked nonzeroOwner notSelf
    nonzeroValue separate bounded)).1, ?_, deposit_storage_ready evm owner keys ready ownerKey⟩
  rw [deposit_projection evm owner keys present ready ownerKey unlocked bounded funds]
  exact .deposit (deposit_enabled evm owner keys ownerKey nonzeroOwner notSelf nonzeroValue bounded funds)

end Rollup.EVM
