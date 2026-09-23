import semantics.Environment
import proofs.Storage
import Reasoning.Storage

open Solm Ethereum Reasoning.Theory

namespace Rollup.EVM

theorem readWord_equiv {left right : Ethereum.State}
    (maps : accountMapEquiv left.accountMap right.accountMap)
    (self : Address) (slot : UInt256) :
    readWord left self slot = readWord right self slot := by
  exact accountMapEquiv_storage_findD maps self slot ⟨0⟩

theorem account_balance_equiv {left right : Ethereum.State}
    (maps : accountMapEquiv left.accountMap right.accountMap) (self : Address) :
    (left.lookupAccount self).elim (⟨0⟩ : UInt256) (·.balance) =
      (right.lookupAccount self).elim (⟨0⟩ : UInt256) (·.balance) := by
  specialize maps self
  unfold Ethereum.State.lookupAccount
  cases hleft : left.accountMap.find? self <;> cases hright : right.accountMap.find? self <;>
    simp_all [accountEquiv]

/-- Equivalent EVM account maps have the same logical rollup state. -/
theorem project_equiv {left right : Ethereum.State}
    (maps : accountMapEquiv left.accountMap right.accountMap)
    (self : Address) (keys : AccessScope) :
    project left self keys = project right self keys := by
  have pending : pendingLedger left self keys = pendingLedger right self keys := by
    funext owner
    simp only [pendingLedger, readWord_equiv maps]
  have claims : claimLedger left self keys = claimLedger right self keys := by
    funext owner
    simp only [claimLedger, readWord_equiv maps]
  simp only [project, pending, claims, readWord_equiv maps, account_balance_equiv maps]

theorem storageReady_equiv {left right : Ethereum.State}
    (maps : accountMapEquiv left.accountMap right.accountMap)
    (self : Address) (keys : AccessScope) :
    StorageReady left self keys ↔ StorageReady right self keys := by
  simp only [StorageReady, SparseStorage, readWord_equiv maps]

theorem worldBounded_equiv {left right : Ethereum.State}
    (maps : accountMapEquiv left.accountMap right.accountMap) :
    WorldBounded left ↔ WorldBounded right := by
  simp only [WorldBounded, account_balance_equiv maps]

theorem account_code_equiv {left right : Ethereum.State}
    (maps : accountMapEquiv left.accountMap right.accountMap) (self : Address) :
    (left.lookupAccount self).map (·.code) = (right.lookupAccount self).map (·.code) := by
  specialize maps self
  unfold Ethereum.State.lookupAccount
  cases hleft : left.accountMap.find? self <;> cases hright : right.accountMap.find? self <;>
    simp_all [accountEquiv]

theorem ownCode_equiv {left right : Ethereum.State}
    (maps : accountMapEquiv left.accountMap right.accountMap)
    (environments : left.executionEnv = right.executionEnv) :
    OwnCode left ↔ OwnCode right := by
  simp only [OwnCode, environments, account_code_equiv maps]

end Rollup.EVM
