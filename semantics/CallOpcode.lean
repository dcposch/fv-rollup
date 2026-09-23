import semantics.CallEntry

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- Read the helper arguments from a call opcode and its stack. -/
def CallSite.decode (state : Ethereum.State) (cost : Nat) (op : Operation) : Option CallSite :=
  match op with
  | .CALL =>
    match state.machineState.stack.pop7 with
    | none => none
    | some (_, gas, target, value, inOffset, inSize, outOffset, outSize) =>
      some {
        gasCost := cost, blobs := state.executionEnv.blobVersionedHashes,
        gas := gas, source := .ofNat state.executionEnv.codeOwner,
        recipient := target, target := target, value := value, contextValue := value,
        inOffset := inOffset, inSize := inSize, outOffset := outOffset, outSize := outSize,
        writable := state.executionEnv.perm }
  | .CALLCODE =>
    match state.machineState.stack.pop7 with
    | none => none
    | some (_, gas, target, value, inOffset, inSize, outOffset, outSize) =>
      some {
        gasCost := cost, blobs := state.executionEnv.blobVersionedHashes,
        gas := gas, source := .ofNat state.executionEnv.codeOwner,
        recipient := .ofNat state.executionEnv.codeOwner, target := target,
        value := value, contextValue := value,
        inOffset := inOffset, inSize := inSize, outOffset := outOffset, outSize := outSize,
        writable := state.executionEnv.perm }
  | .DELEGATECALL =>
    match state.machineState.stack.pop6 with
    | none => none
    | some (_, gas, target, inOffset, inSize, outOffset, outSize) =>
      some {
        gasCost := cost, blobs := state.executionEnv.blobVersionedHashes,
        gas := gas, source := .ofNat state.executionEnv.source,
        recipient := .ofNat state.executionEnv.codeOwner, target := target,
        value := ⟨0⟩, contextValue := state.executionEnv.weiValue,
        inOffset := inOffset, inSize := inSize, outOffset := outOffset, outSize := outSize,
        writable := state.executionEnv.perm }
  | .STATICCALL =>
    match state.machineState.stack.pop6 with
    | none => none
    | some (_, gas, target, inOffset, inSize, outOffset, outSize) =>
      some {
        gasCost := cost, blobs := state.executionEnv.blobVersionedHashes,
        gas := gas, source := .ofNat state.executionEnv.codeOwner,
        recipient := target, target := target, value := ⟨0⟩, contextValue := ⟨0⟩,
        inOffset := inOffset, inSize := inSize, outOffset := outOffset, outSize := outSize,
        writable := false }
  | _ => none

/-- The opcode increments the instruction count before it calls the helper. -/
def callParent (state : Ethereum.State) : Ethereum.State :=
  { state with machineState.execLength := state.machineState.execLength + 1 }

end Rollup.EVM
