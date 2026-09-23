import proofs.RuntimeReturn

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Rollup.EVM

inductive ScalarGetter where
  | stateRoot | batchNumber | backing

def scalarEntry : ScalarGetter → UInt256
  | .stateRoot => ⟨228⟩
  | .batchNumber => ⟨263⟩
  | .backing => ⟨315⟩

def scalarSlot : ScalarGetter → UInt256
  | .stateRoot => ⟨1⟩
  | .batchNumber => ⟨2⟩
  | .backing => ⟨3⟩

def scalarSelector : ScalarGetter → UInt256
  | .stateRoot => ⟨0x9588eca2⟩
  | .batchNumber => ⟨0xba873065⟩
  | .backing => ⟨0xc9503fe2⟩

open Lean in
macro "runtime_cases_run " getter:term " from " base:term " with " "[" steps:evmStep,* "]" : term => do
  let mut acc := base
  let target ← `(Lean.Parser.Tactic.elimTarget| $getter:term)
  let dec ← `(by cases $target <;> decide +kernel)
  for step in steps.getElems do
    match step with
    | `(evmStep| raw $op:ident $args*) => acc ← `($(acc).$op $args*)
    | `(evmStep| $op:ident $args*) =>
      match op.getId with
      | `jump => acc ← `($(acc).jump $dec $(args[0]!) (by evm_ov))
      | `jumpiT => acc ← `($(acc).jumpiT $dec $(args[0]!) $(args[1]!) (by evm_ov))
      | `jumpiNT => acc ← `($(acc).jumpiNT $dec $(args[0]!) (by evm_ov))
      | _ => acc ← `($(acc).$op $args* $dec (by evm_ov))
    | _ => Macro.throwUnsupported
  return acc

private theorem scalar_guard_destination (getter : ScalarGetter) :
    (D_J runtimeBytecode 0).contains (scalarEntry getter + ⟨11⟩) = true := by
  cases getter with
  | stateRoot => exact jumpScan_valid runtimeBytecode 239 350 (by decide +kernel)
  | batchNumber => exact jumpScan_valid runtimeBytecode 274 350 (by decide +kernel)
  | backing => exact jumpScan_valid runtimeBytecode 326 350 (by decide +kernel)

/-- The scalar getter entries reject call value. -/
theorem scalar_getter_nonpayable {I : ExecutionEnv} {g : Sat256} {s0 : Ethereum.State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (getter : ScalarGetter) (rest : List UInt256) (space : rest.length + 3 ≤ 1024)
    (value : I.weiValue ≠ ⟨0⟩)
    (reached : RD runtimeBytecode I g s0 (scalarEntry getter) rest mem aw rdata acc k C) :
    RDrev runtimeBytecode g s0 := by
  have guarded := runtime_cases_run getter from reached with [jumpdest, callvalue, dup1, iszero,
    push2 (scalarEntry getter + ⟨11⟩)]
  have rejected := runtime_cases_run getter from guarded with [jumpiNT (isZero_eq_zero_of_ne value), push0, dup1]
  exact rejected.rev 0 (by cases getter <;> decide +kernel)
    (fun s _ stack => memExpRevert0 s stack) (by evm_ov)

/-- Each scalar getter returns its storage word and preserves accounts. -/
theorem scalar_getter_return {I : ExecutionEnv} {g : Sat256} {s0 : Ethereum.State}
    {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : Nat}
    (getter : ScalarGetter) (rest : List UInt256) (space : rest.length + 4 ≤ 1024)
    (value : I.weiValue = ⟨0⟩)
    (reached : RD runtimeBytecode I g s0 (scalarEntry getter) rest solcFreePtrMem
      (UInt256.ofNat 3) rdata (cA, σ) k C) :
    RDret runtimeBytecode g s0 (cA, σ) (UInt256.toByteArray (solcSlotWord σ I (scalarSlot getter))) := by
  have guarded := runtime_cases_run getter from reached with [jumpdest, callvalue, dup1, iszero,
    push2 (scalarEntry getter + ⟨11⟩)]
  have accepted := runtime_cases_run getter from guarded with [
    jumpiT (by rw [value]; decide) (scalar_guard_destination getter), jumpdest, pop,
    push2 ⟨249⟩, push1 (scalarSlot getter)]
  obtain ⟨_, _, loaded⟩ := accepted.sload (by cases getter <;> decide +kernel) (by evm_ov)
  have returning := runtime_cases_run getter from loaded with [dup2,
    jump (jumpScan_valid runtimeBytecode 249 270 (by decide +kernel))]
  exact runtime_return_word _ (⟨249⟩ :: rest) (by evm_ov)
    solcFreePtrMem_mload64 rfl (solcReturnMem_mload64 _) (solcReturnMem_read128 _) returning

end Rollup.EVM
