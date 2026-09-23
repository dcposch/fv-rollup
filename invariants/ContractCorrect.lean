import semantics.AccountFrame
import semantics.TransactionCodeEntry
import semantics.RootEntryPath
import invariants.TraceObligations
import semantics.ActivePrefix
import semantics.WithdrawalState
import invariants.TreeBoundary

open Ethereum Ethereum.EVM Reasoning.Theory

namespace Rollup.EVM

/-- Exact call labels, financial effects, return values, and failure rollback. -/
def RootInvocationCorrect (self : Address) (keys : AccessScope) (root : Ethereum.State) : Prop :=
  ∃ call : MessageCall,
    root = call.codeEntry runtimeBytecode ∧ MessageEnvironment self call ∧
    ∀ result : MessageResult, call.selectedRun = result.tuple →
      BoundaryRefines self keys call.accounts result.accounts ∧
        (ExecutionEvent.message call result).refined keys

/-- Receiver execution preserves locked storage and backs credit with ETH plus the payment. -/
def RootPaymentCorrect (self : Address) (keys : AccessScope) (root : Ethereum.State) : Prop :=
  ∀ cursor child current : Ethereum.State,
    ContinuingPrefix (D_J runtimeBytecode 0) root cursor →
    ChildCallEntry (D_J runtimeBytecode 0) cursor child → ActivePrefix child current →
    CodeStorageFrame self (withdrawalLockedState root).accountMap current.accountMap ∧
    ∃ owner : Address,
      UInt256.ofNat owner.val = calldataWord root.executionEnv.calldata 4 ∧
      Safe (inFlightProjection current self keys
        ⟨owner, (calldataWord root.executionEnv.calldata 36).toNat, (project root self keys).eth⟩)

/-- Observe any first active root invocation through actual transaction, call, and creation entries. -/
def TransactionObservationsCorrect (event : TransactionEvent) (self : Address) (keys : AccessScope) : Prop :=
  ∀ start root : Ethereum.State,
    TransactionCodeEntry event start → CoveredRootEntryPath self keys root start →
    RootInvocationCorrect self keys root ∧ RootPaymentCorrect self keys root

/-- Full contract target: deployment, complete transactions, labeled calls, and active payments.
    The finite key set covers completed execution and each observed invocation path. -/
def DeployedContractCorrect : Prop :=
  ∀ (deployment : Deployment) (sequencer : Address) (root : Root)
    (keys : AccessScope) (self : Address) (created : Batteries.RBSet AccountAddress compare)
    (accounts : AccountMap) (gas : UInt256) (substate : Substate) (data : ByteArray)
    (events : List TransactionEvent) (after : AccountMap),
    fixedKeys ⊆ keys → NoAlias keys → sequencer ≠ 0 →
    deployment.fresh (deploymentCode sequencer root) →
    (deployment.accounts.find? deployment.sender).isSome →
    WorldBounded (accountView self deployment.accounts) → self ∉ π →
    deployment.run (deploymentCode sequencer root) =
      (self, created, accounts, gas, substate, true, data) →
    TransactionSequence self accounts events after → (∀ event ∈ events, event.scope self ⊆ keys) →
    BoundaryReady self after keys ∧ Safe (boundaryModel self after keys) ∧
      CallTrace (initial self sequencer root (deployment.accounts.findD self default).balance.toNat)
        (boundaryModel self after keys) ∧
      ∀ event : TransactionEvent, event.before = after → event.admissible self →
        TransactionObservationsCorrect event self keys

end Rollup.EVM
