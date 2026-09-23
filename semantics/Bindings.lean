import semantics.Calls
import semantics.Storage

namespace Rollup.EVM

def rootValue (root : Root) : Solm.Value :=
  .fixedBytes ⟨31, by decide⟩ (Ethereum.UInt256.toByteArray ⟨root⟩).toList

def entryIndex : Entry → Nat
  | .deposit _ => 0
  | .executeBatch _ => 1
  | .withdrawPendingBalance _ _ => 2
  | .read .sequencer => 3
  | .read .stateRoot => 4
  | .read .batchNumber => 5
  | .read .backing => 6
  | .read (.pendingDeposits _) => 7
  | .read (.pendingWithdrawals _) => 8

def entryTransition (entry : Entry) : Solm.TransitionDecl :=
  contract.transitions[entryIndex entry]!

def entryArguments : Entry → List Solm.Value
  | .deposit owner => [.address owner]
  | .executeBatch b =>
      [.int b.number, rootValue b.oldRoot, rootValue b.newRoot,
       .address b.depositOwner, .int b.depositAmount,
       .address b.withdrawalOwner, .int b.withdrawalAmount]
  | .withdrawPendingBalance owner amount => [.address owner, .int amount]
  | .read (.pendingDeposits owner) => [.address owner]
  | .read (.pendingWithdrawals owner) => [.address owner]
  | .read _ => []

def entryKeys : Entry → AccessScope
  | .deposit owner => {.pending owner}
  | .executeBatch b => {.pending b.depositOwner, .claims b.withdrawalOwner}
  | .withdrawPendingBalance owner _ => {.claims owner}
  | .read (.pendingDeposits owner) => {.pending owner}
  | .read (.pendingWithdrawals owner) => {.claims owner}
  | .read _ => ∅

def returnValues : ReturnValue → Option (List Solm.Value)
  | .unit => none
  | .address a => some [.address a]
  | .word n => some [.int n]
  | .root r => some [rootValue r]

/-- Bind external arguments in the order used by the ABI decoder. -/
def entryArgumentStore (entry : Entry) : Option Solm.Store :=
  ABI.decodeCalldata.insertValues ((entryTransition entry).params.map Solm.Param.name)
    (entryArguments entry) ∅

/-- Bind the call label to the selector, decoded arguments, sender, and value. -/
def CallBound (evm : Ethereum.State) (locals : Solm.Store) (call : Call) : Prop :=
  let transition := entryTransition call.entry
  call.caller = evm.executionEnv.source ∧
  call.value = evm.executionEnv.weiValue.toNat ∧
  Solm.selectorDispatchMsg contract evm.executionEnv.calldata = some transition ∧
  ABI.decodeCalldataWithMode config.abiDecodeMode (transition.params.map Solm.Param.name)
    (Solm.transitionSignature transition).paramTypes evm.executionEnv.calldata = some locals ∧
  entryArgumentStore call.entry = some locals

/-- Incoming ETH is already in the EVM balance at the function entry. -/
def beforeCall (evm : Ethereum.State) (keys : AccessScope) : State :=
  let s := project evm evm.executionEnv.codeOwner keys
  { s with eth := s.eth - evm.executionEnv.weiValue.toNat }

end Rollup.EVM
