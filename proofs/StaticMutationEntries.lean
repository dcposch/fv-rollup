import proofs.StaticMutationGuards
import proofs.BatchEntry
import proofs.WithdrawalEntry
import proofs.RuntimeAddressAnyDecode
import proofs.GetterCallBinding

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2048
set_option maxHeartbeats 2000000

namespace Rollup.EVM

/-- No static batch succeeds, for valid or malformed calldata. -/
theorem batch_static_no_success {cA gh bl σ σ₀ A I} {g : UInt256}
    {cA' σ' gas substate output} (code : I.code = runtimeBytecode)
    (readonly : I.perm = false) (bounded : I.calldata.size < UInt256.size)
    (selector : solcSelectorWord I = ⟨0x88af9950⟩)
    (success : Ξ cA gh bl σ σ₀ g A I = .ok (.success (cA', σ', gas, substate) output)) : False := by
  obtain ⟨state, execution⟩ := xi_success_execution success
  rw [code] at execution
  rcases batch_entry_classification (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) code bounded selector with
    rejected | ⟨_, _, _, _, _, _, _, reached⟩
  · exact rd_revert_no_success rejected state output execution
  · exact batch_static_guard _ (by simp [batchDecodedStack]) readonly reached state output execution

/-- No static withdrawal succeeds, for valid or malformed calldata. -/
theorem withdrawal_static_no_success {cA gh bl σ σ₀ A I} {g : UInt256}
    {cA' σ' gas substate output} (code : I.code = runtimeBytecode)
    (readonly : I.perm = false) (bounded : I.calldata.size < UInt256.size)
    (selector : solcSelectorWord I = ⟨0xbb3ef682⟩)
    (success : Ξ cA gh bl σ σ₀ g A I = .ok (.success (cA', σ', gas, substate) output)) : False := by
  obtain ⟨state, execution⟩ := xi_success_execution success
  rw [code] at execution
  rcases withdrawal_entry_classification (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) code bounded selector with
    rejected | ⟨_, _, _, _, _, _, reached⟩
  · exact rd_revert_no_success rejected state output execution
  · exact withdrawal_static_guard _ (by simp) readonly reached state output execution

/-- No static deposit succeeds, for valid or malformed calldata. -/
theorem deposit_static_no_success {cA gh bl σ σ₀ A I} {g : UInt256}
    {cA' σ' gas substate output} (code : I.code = runtimeBytecode)
    (readonly : I.perm = false) (bounded : I.calldata.size < UInt256.size)
    (selector : solcSelectorWord I = ⟨0xf340fa01⟩)
    (success : Ξ cA gh bl σ σ₀ g A I = .ok (.success (cA', σ', gas, substate) output)) : False := by
  obtain ⟨state, execution⟩ := xi_success_execution success
  rw [code] at execution
  have length := runtime_success_length code success
  obtain ⟨_, _, decoder⟩ := runtime_deposit_dispatch (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) code length bounded selector
  rcases runtime_address_decode_any ⟨393⟩ [⟨226⟩, ⟨0xf340fa01⟩]
      (jumpScan_valid runtimeBytecode 393 410 (by decide +kernel)) (by decide) decoder with
    rejected | ⟨_, _, _, decoded⟩
  · exact rd_revert_no_success rejected state output execution
  · have entered := runtime_run decoded with [jumpdest, push2 ⟨1045⟩,
      jump (jumpScan_valid runtimeBytecode 1045 1060 (by decide +kernel))]
    exact deposit_static_guard _ (by simp) readonly entered state output execution

end Rollup.EVM
