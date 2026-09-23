import semantics.Environment
import proofs.Storage

open Ethereum Reasoning.Theory

namespace Rollup.EVM

theorem lookup_store_other (evm : Ethereum.State) (self other : Address) (slot value : UInt256)
    (different : other ≠ self) :
    (Solm.EVM.storageStore evm self slot value).lookupAccount other = evm.lookupAccount other := by
  unfold Solm.EVM.storageStore
  cases h : evm.lookupAccount self with
  | none => rfl
  | some acc =>
    simp only [Option.option, Ethereum.State.setAccount, Ethereum.State.lookupAccount]
    exact accountMap_find?_insert_ne _ other self _ different

theorem all_balances_store (evm : Ethereum.State) (self other : Address) (slot value : UInt256) :
    ((Solm.EVM.storageStore evm self slot value).lookupAccount other).map (·.balance) =
      (evm.lookupAccount other).map (·.balance) := by
  by_cases same : other = self
  · subst other
    exact balance_store evm self slot value
  · rw [lookup_store_other evm self other slot value same]

theorem all_codes_store (evm : Ethereum.State) (self other : Address) (slot value : UInt256) :
    ((Solm.EVM.storageStore evm self slot value).lookupAccount other).map (·.code) =
      (evm.lookupAccount other).map (·.code) := by
  by_cases same : other = self
  · subst other
    rw [lookup_store_self]
    cases h : evm.lookupAccount self with
    | none => rfl
    | some acc => simp [Account.updateStorage]; split <;> rfl
  · rw [lookup_store_other evm self other slot value same]

theorem worldBounded_store (evm : Ethereum.State) (self : Address) (slot value : UInt256)
    (bound : WorldBounded evm) : WorldBounded (Solm.EVM.storageStore evm self slot value) := by
  have balances (other : Address) :
      (((Solm.EVM.storageStore evm self slot value).lookupAccount other).elim
        (⟨0⟩ : UInt256) (·.balance)).toNat =
      ((evm.lookupAccount other).elim (⟨0⟩ : UInt256) (·.balance)).toNat := by
    have same := all_balances_store evm self other slot value
    cases h1 : (Solm.EVM.storageStore evm self slot value).lookupAccount other <;>
      cases h2 : evm.lookupAccount other <;> simp_all
  simpa only [WorldBounded, balances] using bound

theorem ownCode_store (evm : Ethereum.State) (self : Address) (slot value : UInt256)
    (code : OwnCode evm) :
    OwnCode (Solm.EVM.storageStore evm self slot value) := by
  simp only [OwnCode, storageStore_executionEnv, all_codes_store]
  exact code

end Rollup.EVM
