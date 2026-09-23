import semantics.Semantics
import semantics.Model

namespace Rollup.EVM

inductive StorageKey where
  | fixed : Fin 7 → StorageKey
  | pending : Address → StorageKey
  | claims : Address → StorageKey
  deriving DecidableEq

abbrev AccessScope := Finset StorageKey

def keySlot : StorageKey → Ethereum.UInt256
  | .fixed slot => Ethereum.UInt256.ofNat slot.val
  | .pending owner => mapSlot (.address owner) ⟨4⟩
  | .claims owner => mapSlot (.address owner) ⟨5⟩

def fixedKeys : AccessScope := Finset.univ.image StorageKey.fixed

/-- Require distinct physical slots only for keys in this finite scope. -/
def NoAlias (keys : AccessScope) : Prop :=
  ∀ a ∈ keys, ∀ b ∈ keys, keySlot a = keySlot b → a = b

def readWord (evm : Ethereum.State) (self : Address) (slot : Ethereum.UInt256) : Ethereum.UInt256 :=
  Solm.EVM.storageLoad evm self slot

/-- Slots outside the recorded write scope are zero after fresh deployment. -/
def SparseStorage (evm : Ethereum.State) (self : Address) (keys : AccessScope) : Prop :=
  ∀ slot, (∀ key ∈ keys, keySlot key ≠ slot) → readWord evm self slot = ⟨0⟩

def pendingLedger (evm : Ethereum.State) (self : Address) (keys : AccessScope) : Ledger :=
  fun a => if StorageKey.pending a ∈ keys then
    (readWord evm self (keySlot (.pending a))).toNat else 0

def claimLedger (evm : Ethereum.State) (self : Address) (keys : AccessScope) : Ledger :=
  fun a => if StorageKey.claims a ∈ keys then
    (readWord evm self (keySlot (.claims a))).toNat else 0

/-- Read logical credit only at tracked keys. Other accounts have zero credit. -/
def project (evm : Ethereum.State) (self : Address) (keys : AccessScope) : State :=
  { self := self
    sequencer := Ethereum.AccountAddress.ofUInt256 (readWord evm self ⟨0⟩)
    root := (readWord evm self ⟨1⟩).val
    batchNumber := (readWord evm self ⟨2⟩).toNat
    backing := (readWord evm self ⟨3⟩).toNat
    pending := pendingLedger evm self keys
    claims := claimLedger evm self keys
    eth := ((evm.lookupAccount self).elim (⟨0⟩ : Ethereum.UInt256) (fun acc => acc.balance)).toNat
    payment := none }

/-- Include every written slot and each mapping key used by the current call. -/
def StorageReady (evm : Ethereum.State) (self : Address) (keys : AccessScope) : Prop :=
  fixedKeys ⊆ keys ∧ NoAlias keys ∧ SparseStorage evm self keys

end Rollup.EVM
