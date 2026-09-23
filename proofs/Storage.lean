import semantics.Storage
import Reasoning.Storage

open Ethereum Reasoning.Theory

namespace Rollup.EVM

theorem noAlias_mono {small large : AccessScope} (subset : small ⊆ large)
    (distinct : NoAlias large) : NoAlias small := by
  intro a ha b hb same
  exact distinct a (subset ha) b (subset hb) same

theorem fresh_key_zero {evm : Ethereum.State} {self : Address} {small large : AccessScope}
    (subset : small ⊆ large) (distinct : NoAlias large)
    (sparse : SparseStorage evm self small) {key : StorageKey}
    (newKey : key ∈ large) (notOld : key ∉ small) :
    readWord evm self (keySlot key) = ⟨0⟩ := by
  apply sparse
  intro old oldMem same
  have equal := distinct old (subset oldMem) key newKey same
  exact notOld (equal ▸ oldMem)

theorem pending_untracked (evm : Ethereum.State) (self : Address)
    (keys : AccessScope) (owner : Address) (h : StorageKey.pending owner ∉ keys) :
    (project evm self keys).pending owner = 0 := by
  simp [project, pendingLedger, h]

theorem claims_untracked (evm : Ethereum.State) (self : Address)
    (keys : AccessScope) (owner : Address) (h : StorageKey.claims owner ∉ keys) :
    (project evm self keys).claims owner = 0 := by
  simp [project, claimLedger, h]

/-- Extending the read scope cannot create logical credit. -/
theorem project_extend {evm : Ethereum.State} {self : Address} {small large : AccessScope}
    (subset : small ⊆ large) (distinct : NoAlias large)
    (sparse : SparseStorage evm self small) :
    project evm self large = project evm self small := by
  have hp : pendingLedger evm self large = pendingLedger evm self small := by
    funext a
    by_cases old : StorageKey.pending a ∈ small
    · simp [pendingLedger, old, subset old]
    · by_cases fresh : StorageKey.pending a ∈ large
      · have zero := fresh_key_zero subset distinct sparse fresh old
        simp [pendingLedger, old, fresh, zero, Ethereum.UInt256.toNat]
      · simp [pendingLedger, old, fresh]
  have hc : claimLedger evm self large = claimLedger evm self small := by
    funext a
    by_cases old : StorageKey.claims a ∈ small
    · simp [claimLedger, old, subset old]
    · by_cases fresh : StorageKey.claims a ∈ large
      · have zero := fresh_key_zero subset distinct sparse fresh old
        simp [claimLedger, old, fresh, zero, Ethereum.UInt256.toNat]
      · simp [claimLedger, old, fresh]
  simp only [project, hp, hc]

theorem sparse_mono {evm : Ethereum.State} {self : Address} {small large : AccessScope}
    (subset : small ⊆ large) (sparse : SparseStorage evm self small) :
    SparseStorage evm self large := by
  intro slot disjoint
  exact sparse slot (fun key h => disjoint key (subset h))

theorem noAlias_fixed : NoAlias fixedKeys := by
  intro a ha b hb same
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hb
  apply congrArg StorageKey.fixed
  apply Fin.ext
  have hi : i.val < UInt256.size := lt_trans i.isLt (by decide)
  have hj : j.val < UInt256.size := lt_trans j.isLt (by decide)
  have h := congrArg UInt256.toNat same
  simpa [keySlot, UInt256.ofNat, UInt256.toNat, Id.run, Nat.mod_eq_of_lt hi,
    Nat.mod_eq_of_lt hj] using h

theorem lookup_store_self (evm : Ethereum.State) (self : Address) (slot value : UInt256) :
    (Solm.EVM.storageStore evm self slot value).lookupAccount self =
      (evm.lookupAccount self).map (fun acc => acc.updateStorage slot value) := by
  unfold Solm.EVM.storageStore
  cases h : evm.lookupAccount self with
  | none => simpa using h
  | some acc =>
    simp only [Option.option, Option.map_some, Ethereum.State.setAccount,
      Ethereum.State.lookupAccount]
    exact accountMap_find_insert_self _ _ _

theorem balance_store (evm : Ethereum.State) (self : Address) (slot value : UInt256) :
    ((Solm.EVM.storageStore evm self slot value).lookupAccount self).map (·.balance) =
      (evm.lookupAccount self).map (·.balance) := by
  rw [lookup_store_self]
  cases h : evm.lookupAccount self with
  | none => rfl
  | some acc => simp [Account.updateStorage]; split <;> rfl

theorem sparse_store {evm : Ethereum.State} {self : Address} {keys : AccessScope}
    (sparse : SparseStorage evm self keys) {key : StorageKey} (member : key ∈ keys)
    (value : UInt256) :
    SparseStorage (Solm.EVM.storageStore evm self (keySlot key) value) self keys := by
  intro slot outside
  change Solm.EVM.storageLoad _ _ _ = _
  rw [storageLoad_storageStore_ne _ _ (Ne.symm (outside key member))]
  exact sparse slot outside

theorem read_store_key {evm : Ethereum.State} {self : Address} {keys : AccessScope}
    {acc : Account} (present : evm.lookupAccount self = some acc)
    (distinct : NoAlias keys) {readKey writeKey : StorageKey}
    (readMem : readKey ∈ keys) (writeMem : writeKey ∈ keys) (value : UInt256) :
    readWord (Solm.EVM.storageStore evm self (keySlot writeKey) value) self (keySlot readKey) =
      if readKey = writeKey then value else readWord evm self (keySlot readKey) := by
  by_cases same : readKey = writeKey
  · subst readKey
    simpa [readWord] using storageLoad_storageStore_same_present evm self present (keySlot writeKey) value
  · have different : keySlot readKey ≠ keySlot writeKey :=
      fun h => same (distinct readKey readMem writeKey writeMem h)
    simpa [readWord, same] using storageLoad_storageStore_ne evm self different (val := value)

/-- Write an address to a fresh slot with a kernel-checked byte calculation. -/
theorem store_address_fresh (evm : Ethereum.State) (slot address : UInt256)
    (canonical : address.toNat < _root_.EVM.addressModulus)
    (fresh : readWord evm evm.executionEnv.codeOwner slot = ⟨0⟩) :
    Solm.storageLocStore evm (addressOffset0Loc slot)
      (.address (AccountAddress.ofNat address.toNat)) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot address) := by
  unfold Solm.storageLocStore Solm.storageLocWriteWord addressOffset0Loc
  simp only [valueToWord_address_ofNat_canonical address canonical, bind, Option.bind]
  congr 2
  apply u256_inj
  show fromBytes'
      (List.take 0 _ ++ List.take 20 _ ++ List.drop 20 _) = address.toNat
  rw [List.take_zero, List.nil_append, fromBytes'_append,
    fromBytes'_take_wordLE, fromBytes'_drop_wordLE]
  rw [show Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot = ⟨0⟩ from fresh]
  simp only [show (⟨0⟩ : UInt256).toNat = 0 from rfl, Nat.zero_div, Nat.mul_zero, Nat.add_zero]
  apply Nat.mod_eq_of_lt
  simpa [_root_.EVM.addressModulus, _root_.EVM.twoPow] using canonical

end Rollup.EVM
