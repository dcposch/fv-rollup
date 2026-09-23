import semantics.Boundary
import semantics.CallScope
import Ethereum.Theory.AccountLocality

open Ethereum Ethereum.EVM Solm

namespace Rollup.EVM

structure MessageResult where
  created : Batteries.RBSet AccountAddress compare
  accounts : AccountMap
  gas : UInt256
  substate : Substate
  accepted : Bool
  output : ByteArray

def MessageResult.tuple (result : MessageResult) :=
  (result.created, result.accounts, result.gas, result.substate, result.accepted, result.output)

/-- Conditions for a funded call in the rollup's own storage context. -/
def MessageEnvironment (self : Address) (call : MessageCall) : Prop :=
  call.receiver = self ∧ call.receiver ≠ call.sender ∧ call.contextValue = call.value ∧
  call.value.toNat ≤ (call.accounts.findD call.sender default).balance.toNat ∧
  call.calldata.size < UInt256.size

inductive ExecutionEvent where
  | message (call : MessageCall) (result : MessageResult)
  | donation (sender : Address) (value : UInt256)
  | selfdestruct (sender : Address)
  | rejected (call : MessageCall) (result : MessageResult)

/-- Record completed messages, funded transfers, and actual self-destruct instructions. -/
inductive ExecutionStep (self : Address) : ExecutionEvent → AccountMap → AccountMap → Prop where
  | message (call : MessageCall) (result : MessageResult)
      (environment : MessageEnvironment self call)
      (executed : call.selectedRun = result.tuple) :
      ExecutionStep self (.message call result) call.accounts result.accounts
  | donation (accounts : AccountMap) (sender : Address) (value : UInt256)
      (different : self ≠ sender)
      (funds : value.toNat ≤ (accounts.findD sender default).balance.toNat) :
      ExecutionStep self (.donation sender value) accounts (sendEth self sender value true accounts)
  | selfdestruct {before after : Ethereum.State} {jumps : Array UInt256}
      {arg : Option (UInt256 × Nat)} {ret : Option (HaltCause × ByteArray)}
      (different : self ≠ before.executionEnv.codeOwner)
      (decoded : (decode before.executionEnv.code before.machineState.pc).getD (.STOP, none) =
        (.SELFDESTRUCT, arg))
      (executed : Xstep jumps before = .ok (after, ret)) :
      ExecutionStep self (.selfdestruct before.executionEnv.codeOwner) before.accountMap after.accountMap
  | rejected (call : MessageCall) (result : MessageResult)
      (rejected : result.accepted = false) (executed : call.selectedRun = result.tuple) :
      ExecutionStep self (.rejected call result) call.accounts result.accounts

/-- Finite execution at completed-call boundaries. Message calls include their full call trees. -/
inductive ExecutionTrace (self : Address) (start : AccountMap) :
    List ExecutionEvent → AccountMap → Prop where
  | initial : ExecutionTrace self start [] start
  | next {events before after event} : ExecutionTrace self start events before →
      ExecutionStep self event before after → ExecutionTrace self start (events ++ [event]) after

def ExecutionEvent.covered (event : ExecutionEvent) (keys : AccessScope) : Prop :=
  match event with
  | .message call _ => CalldataCovered call.entryState keys
  | .donation _ _ => True
  | .selfdestruct _ => True
  | .rejected _ _ => True

/-- Successful calls have exact decoded effects. Rejected calls roll back accounts and substate. -/
def ExecutionEvent.refined (event : ExecutionEvent) (keys : AccessScope) : Prop :=
  match event with
  | .message call result =>
      if result.accepted then
        ∃ locals label value payments,
          CallBound call.entryState locals label ∧
          CallStep (boundaryModel call.receiver call.accounts keys) label (.success value) payments
            (boundaryModel call.receiver result.accounts keys) ∧
          returnDataEquiv result.output (returnValues value) (.abi (entryTransition label.entry).returnType)
      else result.accounts = call.accounts ∧ result.substate = call.substate
  | .donation _ _ => True
  | .selfdestruct _ => True
  | .rejected call result => result.accounts = call.accounts ∧ result.substate = call.substate

end Rollup.EVM
