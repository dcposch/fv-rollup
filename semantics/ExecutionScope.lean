import semantics.ExecutionRecord

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- Collect the keys from the code frame and every nested frame of a message. -/
noncomputable def messageCodeScope (call : MessageCall) (code : ByteArray) (self : Address) : AccessScope :=
  (executionRecord ((call.codeEntry code).machineState.gasAvailable.toNat + 1)
    (D_J code 0) (call.codeEntry code)).scope self

/-- Precompiles have no nested code frames. Other messages use the actually selected code. -/
noncomputable def selectedMessageScope (call : MessageCall) (self : Address) : AccessScope :=
  match toExecute call.accounts call.receiver with
  | .Precompiled _ => ∅
  | .Code code => messageCodeScope call code self

/-- Collect the keys from initialization and every nested frame. -/
noncomputable def creationExecutionScope (call : CreationCall) (self : Address) : AccessScope :=
  (executionRecord (call.entryState.machineState.gasAvailable.toNat + 1)
    (D_J call.environment.code 0) call.entryState).scope self

end Rollup.EVM
