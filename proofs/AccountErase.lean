-- Lookup lemmas adapted from pinned EVMLean, Ethereum/Theory/StorageExtensionality.lean.
import proofs.TreeErase

open Ethereum Ethereum.EVM

namespace Rollup.EVM

theorem account_erase_toList_filter (st : AccountMap) (slot : AccountAddress) :
    (st.erase slot).toList = st.toList.filter (fun entry => compare slot entry.1 != .eq) := by
  cases st with
  | mk val wf =>
      exact rbNode_erase_toList_filter val wf.out.1

theorem account_find?_erase_eq (st : AccountMap) (slot query : AccountAddress)
    (hquery : compare query slot = .eq) :
    (st.erase slot).find? query = none := by
  cases hfind : (st.erase slot).find? query with
  | none => rfl
  | some value =>
      obtain ⟨key, hmem, hcmp⟩ := Batteries.RBMap.find?_some_mem_toList hfind
      rw [account_erase_toList_filter st slot] at hmem
      have hnot := (List.mem_filter.mp hmem).2
      have hslotkey : compare slot key = .eq := by
        have hqkey : compare query key = .eq := hcmp
        rw [Std.TransCmp.congr_left hquery] at hqkey
        exact hqkey
      rw [hslotkey] at hnot
      cases hnot

theorem account_find?_erase_ne (st : AccountMap) (slot query : AccountAddress)
    (hquery : compare query slot ≠ .eq) :
    (st.erase slot).find? query = st.find? query := by
  cases h₁ : (st.erase slot).find? query with
  | none =>
      cases h₂ : st.find? query with
      | none => rfl
      | some value =>
          exfalso
          obtain ⟨key, hmem, hcmp⟩ := Batteries.RBMap.find?_some_mem_toList h₂
          have hslotkey_ne : (compare slot key != .eq) = true := by
            by_contra hfalse
            simp at hfalse
            have hqslot : compare query slot = .eq := by
              have hslotkey : compare slot key = .eq := by simpa using hfalse
              have hkeyslot : compare key slot = .eq := by
                have hswap :=
                  (Std.OrientedCmp.eq_swap (cmp := compare) (a := slot) (b := key))
                rw [hslotkey] at hswap
                simpa using hswap.symm
              have hqkey : compare query key = .eq := hcmp
              rw [Std.TransCmp.congr_right hkeyslot] at hqkey
              exact hqkey
            exact hquery hqslot
          have hmemErase : (key, value) ∈ (st.erase slot).toList := by
            rw [account_erase_toList_filter st slot]
            simp [hmem, hslotkey_ne]
          have hfindErase : (st.erase slot).find? query = some value := by
            rw [Batteries.RBMap.find?_some]
            exact ⟨key, hmemErase, hcmp⟩
          rw [h₁] at hfindErase
          contradiction
  | some value =>
      obtain ⟨key, hmem, hcmp⟩ := Batteries.RBMap.find?_some_mem_toList h₁
      rw [account_erase_toList_filter st slot] at hmem
      simp at hmem
      rcases hmem with ⟨hmemOrig, _hnot⟩
      have hfindOrig : st.find? query = some value := by
        rw [Batteries.RBMap.find?_some]
        exact ⟨key, hmemOrig, hcmp⟩
      rw [hfindOrig]

theorem account_find?_erase (st : AccountMap) (slot query : AccountAddress) :
    (st.erase slot).find? query =
      if compare query slot = .eq then none else st.find? query := by
  by_cases h : compare query slot = .eq
  · simp [h, account_find?_erase_eq st slot query h]
  · simp [h, account_find?_erase_ne st slot query h]

end Rollup.EVM
