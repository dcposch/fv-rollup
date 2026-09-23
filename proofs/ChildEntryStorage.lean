import proofs.ActiveCreationEntry
import proofs.ActiveCallEntry

open Ethereum Ethereum.EVM

set_option maxRecDepth 4096

namespace Rollup.EVM

/-- The call precheck and incoming transfer preserve code and storage. -/
theorem child_call_entry_storage {before child : Ethereum.State} {jumps : Array UInt256}
    (entered : ChildCallEntry jumps before child) (self : Address) :
    CodeStorageFrame self before.accountMap child.accountMap := by
  cases entered with
  | @entered op arg checked cost site code instruction precheck arguments enabled selected =>
    have accounts := precheck_accounts precheck
    let parent := callParent { checked with executionEnv.depth := before.executionEnv.depth }
    let call := site.message parent
    have frame := sendEth_accountStaticStateEq call.receiver call.sender call.value true call.accounts self
    change CodeStorageFrame self before.accountMap call.initialAccounts
    exact Eq.mp (congrArg (fun world => CodeStorageFrame self world call.initialAccounts) accounts) frame

/-- Creation entry changes the nonce and ETH but preserves code and storage. -/
theorem child_creation_entry_storage {before child : Ethereum.State} {jumps : Array UInt256}
    (entered : ChildCreationEntry jumps before child) (self : Address) :
    CodeStorageFrame self before.accountMap child.accountMap := by
  cases entered with
  | @entered op arg checked cost site instruction precheck arguments bounded allowed =>
    have accounts := precheck_accounts precheck
    let parent := { checked with executionEnv.depth := before.executionEnv.depth }
    let call := site.call parent cost allowed
    have nonce := incrementNonce_storage checked.accountMap checked.executionEnv.codeOwner self
    have transfer := sendEthCreate_static_state call.address call.sender call.value true call.accounts self
    have frame := nonce.trans transfer
    change CodeStorageFrame self before.accountMap call.initialAccounts
    exact Eq.mp (congrArg (fun world => CodeStorageFrame self world call.initialAccounts) accounts) frame

end Rollup.EVM
