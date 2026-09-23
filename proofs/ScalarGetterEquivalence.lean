import proofs.RuntimeScalarDispatch
import proofs.GetterValues
import Reasoning.Dispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Rollup.EVM

def scalarModelGetter : ScalarGetter → Getter
  | .stateRoot => .stateRoot
  | .batchNumber => .batchNumber
  | .backing => .backing

def scalarValue (getter : ScalarGetter) (word : UInt256) : Value :=
  match getter with
  | .stateRoot => .fixedBytes ⟨31, by decide⟩ (_root_.EVM.Word.toBytesBE word)
  | .batchNumber | .backing => .int word.toNat

/-- Encode a root with kernel-checked ABI facts. -/
theorem root_return_encoding (word : UInt256) :
    encodeReturnValue? (.elem (.bytes ⟨31, by decide⟩))
      (.fixedBytes ⟨31, by decide⟩ (_root_.EVM.Word.toBytesBE word)) =
      some (UInt256.toByteArray word) := by
  have length : (_root_.EVM.Word.toBytesBE word).length = 32 := by
    simpa using word_toBytesBE_toByteArray_size word
  refine scalarReturnEncoding (t := .bytes ⟨31, by decide⟩) (w := word)
    (by decide +kernel) ?_ ?_
  · simp only [abiTupleHeadSize?, staticABIEncodedSize?, isDynamicABIType, bind, Option.bind]
    decide +kernel
  · simp [encodeABIValue?, length, zeroBytes]

theorem scalar_getter_encoding (getter : ScalarGetter) (word : UInt256) :
    returnEquiv (UInt256.toByteArray word) (some [scalarValue getter word])
      (entryTransition (.read (scalarModelGetter getter))).returnType := by
  cases getter with
  | stateRoot => exact returnEquiv_of_encode (root_return_encoding word)
  | batchNumber => exact returnEquiv_of_encode (uint256ReturnEncoding word)
  | backing => exact returnEquiv_of_encode (uint256ReturnEncoding word)

theorem scalar_getter_value_init {cA gh bl σ σ₀ A I} {g : Sat256} (getter : ScalarGetter) :
    getterValue (initState cA gh bl σ σ₀ g A I) (scalarModelGetter getter) =
      scalarValue getter (solcSlotWord σ I (scalarSlot getter)) := by
  cases getter <;> rfl

/-- Scalar getters have equivalent EVM and source outcomes. -/
theorem scalar_getter_equivalence_for {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (getter : ScalarGetter) (code : I.code = runtimeBytecode)
    (length : 4 ≤ I.calldata.size) (bounded : I.calldata.size < UInt256.size)
    (selector : solcSelectorWord I = scalarSelector getter)
    (dispatch : dispatchMsg contract I.calldata =
      some (entryTransition (.read (scalarModelGetter getter))))
    (maps : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have decoded : decodeCalldataWithMode config.abiDecodeMode
      ((entryTransition (.read (scalarModelGetter getter))).params.map Param.name)
      (transitionSignature (entryTransition (.read (scalarModelGetter getter)))).paramTypes
      I.calldata = some (getterLocals (scalarModelGetter getter)) := by
    cases getter <;> exact decodeCalldata_empty_ok length
  obtain ⟨_, _, reached⟩ := scalar_getter_dispatch (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) getter code length bounded selector
  by_cases value : I.weiValue = ⟨0⟩
  · have returned := scalar_getter_return getter [scalarSelector getter] (by simp) value reached
    have source := (getter_source_exact (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
      (scalarModelGetter getter) value).1
    have word : solcSlotWord σ_solm I (scalarSlot getter) =
        solcSlotWord σ_evm I (scalarSlot getter) :=
      (accountMapEquiv_storage_findD maps I.codeOwner (scalarSlot getter) ⟨0⟩).symm
    have values : some [getterValue (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (scalarModelGetter getter)] = some [scalarValue getter (solcSlotWord σ_evm I (scalarSlot getter))] := by
      rw [scalar_getter_value_init, word]
    exact returned.reEquivExecutionTransport code dispatch decoded source values maps
      (scalar_getter_encoding getter _)
  · have rejected := scalar_getter_nonpayable getter [scalarSelector getter] (by simp) value reached
    have source : ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (getterLocals (scalarModelGetter getter))
        (entryTransition (.read (scalarModelGetter getter))).body .reverted := by
      cases getter <;> exact .execBlockRevert (.consRevert (.requireFalse (evalCallvalueEq_false value)))
    exact rejected.reEquivExecutionRevert code dispatch decoded source

end Rollup.EVM
