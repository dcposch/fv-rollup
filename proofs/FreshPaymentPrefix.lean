import proofs.RootCallPrefix
import proofs.PaymentPrefixStorage
import proofs.support.FreshFrame

open Ethereum Ethereum.EVM Reasoning.Theory

namespace Rollup.EVM

/-- A fresh runtime frame reaches a child only through the checked withdrawal prelude. -/
theorem fresh_root_payment_bound {root cursor child : Ethereum.State}
    (fresh : FreshFrame root) (code : root.executionEnv.code = runtimeBytecode)
    (bounded : root.executionEnv.calldata.size < UInt256.size)
    (earlier : ContinuingPrefix (D_J runtimeBytecode 0) root cursor)
    (entered : ChildCallEntry (D_J runtimeBytecode 0) cursor child) :
    WithdrawalCallPrefix root cursor := by
  have bound := root_call_prefix_bound root.createdAccounts root.genesisBlockHeader root.blocks
    root.accountMap root.σ₀ root.substate root.executionEnv root.machineState.gasAvailable
    cursor child
  change root = initState root.createdAccounts root.genesisBlockHeader root.blocks
    root.accountMap root.σ₀ root.machineState.gasAvailable root.substate root.executionEnv at fresh
  rw [← fresh] at bound
  exact bound code bounded earlier entered

/-- All receiver frames preserve the exact locked storage reached by the root prelude. -/
theorem fresh_root_payment_storage {root cursor child current : Ethereum.State} {keys}
    (fresh : FreshFrame root) (bounded : root.executionEnv.calldata.size < UInt256.size)
    (code : OwnCode root) (world : WorldBounded root)
    (ready : StorageReady root root.executionEnv.codeOwner keys)
    (safe : Safe (project root root.executionEnv.codeOwner keys)) (covered : CalldataCovered root keys)
    (earlier : ContinuingPrefix (D_J runtimeBytecode 0) root cursor)
    (entered : ChildCallEntry (D_J runtimeBytecode 0) cursor child) (active : ActivePrefix child current) :
    CodeStorageFrame root.executionEnv.codeOwner (withdrawalLockedState root).accountMap current.accountMap :=
  withdrawal_cursor_active_storage root cursor child current keys _ code world ready safe covered
    (fresh_root_payment_bound fresh code.1 bounded earlier entered) entered active

end Rollup.EVM
