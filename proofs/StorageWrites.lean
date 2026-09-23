import semantics.Environment
import proofs.World

open Ethereum Reasoning.Theory

namespace Rollup.EVM

def storeKeys (evm : Ethereum.State) (self : Address) : List (StorageKey × UInt256) → Ethereum.State
  | [] => evm
  | (key, value) :: rest => storeKeys (Solm.EVM.storageStore evm self (keySlot key) value) self rest

def writtenWord (key : StorageKey) (old : UInt256) : List (StorageKey × UInt256) → UInt256
  | [] => old
  | (writeKey, value) :: rest => writtenWord key (if key = writeKey then value else old) rest

theorem storeKeys_present (evm : Ethereum.State) (self : Address) (writes : List (StorageKey × UInt256))
    (present : ∃ account, evm.lookupAccount self = some account) :
    ∃ account, (storeKeys evm self writes).lookupAccount self = some account := by
  induction writes generalizing evm with
  | nil => exact present
  | cons write rest ih =>
    apply ih
    obtain ⟨account, found⟩ := present
    exact ⟨account.updateStorage (keySlot write.1) write.2, by
      simp [lookup_store_self, found]⟩

/-- A finite write list changes only its tracked keys. -/
theorem read_storeKeys (evm : Ethereum.State) (self : Address) (writes : List (StorageKey × UInt256))
    (keys : AccessScope) (key : StorageKey)
    (present : ∃ account, evm.lookupAccount self = some account)
    (distinct : NoAlias keys) (tracked : key ∈ keys)
    (writesTracked : ∀ write ∈ writes, write.1 ∈ keys) :
    readWord (storeKeys evm self writes) self (keySlot key) =
      writtenWord key (readWord evm self (keySlot key)) writes := by
  induction writes generalizing evm with
  | nil => rfl
  | cons write rest ih =>
    obtain ⟨account, found⟩ := present
    have present' : ∃ account', (Solm.EVM.storageStore evm self (keySlot write.1) write.2).lookupAccount self = some account' :=
      ⟨account.updateStorage (keySlot write.1) write.2, by simp [lookup_store_self, found]⟩
    rw [storeKeys, ih _ present' (fun item member => writesTracked item (by simp [member]))]
    rw [read_store_key found distinct tracked (writesTracked write (by simp))]
    rfl

theorem storeKeys_ready (evm : Ethereum.State) (self : Address) (writes : List (StorageKey × UInt256))
    (keys : AccessScope) (ready : StorageReady evm self keys)
    (writesTracked : ∀ write ∈ writes, write.1 ∈ keys) :
    StorageReady (storeKeys evm self writes) self keys := by
  induction writes generalizing evm with
  | nil => exact ready
  | cons write rest ih =>
    exact ih _ ⟨ready.1, ready.2.1,
      sparse_store ready.2.2 (writesTracked write (by simp)) write.2⟩
      (fun item member => writesTracked item (by simp [member]))

theorem storeKeys_environment (evm : Ethereum.State) (self : Address) (writes : List (StorageKey × UInt256)) :
    (storeKeys evm self writes).executionEnv = evm.executionEnv := by
  induction writes generalizing evm with
  | nil => rfl
  | cons write rest ih =>
    exact (ih _).trans (storageStore_executionEnv ..)

theorem storeKeys_balance (evm : Ethereum.State) (self : Address) (writes : List (StorageKey × UInt256)) :
    ((storeKeys evm self writes).lookupAccount self).map (·.balance) =
      (evm.lookupAccount self).map (·.balance) := by
  induction writes generalizing evm with
  | nil => rfl
  | cons write rest ih => exact (ih _).trans (balance_store ..)

theorem storeKeys_ownCode (evm : Ethereum.State) (self : Address) (writes : List (StorageKey × UInt256))
    (code : OwnCode evm) : OwnCode (storeKeys evm self writes) := by
  induction writes generalizing evm with
  | nil => exact code
  | cons write rest ih => exact ih _ (ownCode_store _ _ _ _ code)

theorem storeKeys_worldBounded (evm : Ethereum.State) (self : Address) (writes : List (StorageKey × UInt256))
    (world : WorldBounded evm) : WorldBounded (storeKeys evm self writes) := by
  induction writes generalizing evm with
  | nil => exact world
  | cons write rest ih => exact ih _ (worldBounded_store _ _ _ _ world)

end Rollup.EVM
