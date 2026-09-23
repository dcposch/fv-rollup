import proofs.AccountErase
import Reasoning.Storage

open Ethereum Ethereum.EVM Reasoning.Theory

namespace Rollup.EVM

private theorem fold_accounts_find_some (entries : List (AccountAddress × Account))
    (initial : AccountMap) (query : AccountAddress) (value : Account)
    (consistent : ∀ entry ∈ entries, entry.1 = query → entry.2 = value)
    (known : initial.find? query = some value ∨ (query, value) ∈ entries) :
    (entries.foldl (fun result entry => result.insert entry.1 entry.2) initial).find? query = some value := by
  induction entries generalizing initial with
  | nil => exact known.resolve_right (List.not_mem_nil)
  | cons entry rest ih =>
    obtain ⟨owner, account⟩ := entry
    have tail : ∀ entry ∈ rest, entry.1 = query → entry.2 = value := by
      intro entry member same
      exact consistent entry (List.mem_cons_of_mem _ member) same
    apply ih _ tail
    by_cases same : query = owner
    · have accountEq := consistent (owner, account) List.mem_cons_self same.symm
      subst owner
      change account = value at accountEq
      subst account
      exact .inl (accountMap_find_insert_self _ _ _)
    · have unchanged := accountMap_find?_insert_ne initial query owner account same
      rcases known with before | member
      · exact .inl (unchanged.trans before)
      · rcases List.mem_cons.mp member with equal | member
        · exact (same (congrArg Prod.fst equal)).elim
        · exact .inr member

private theorem fold_accounts_find_none (entries : List (AccountAddress × Account))
    (initial : AccountMap) (query : AccountAddress)
    (different : ∀ entry ∈ entries, entry.1 ≠ query) (empty : initial.find? query = none) :
    (entries.foldl (fun result entry => result.insert entry.1 entry.2) initial).find? query = none := by
  induction entries generalizing initial with
  | nil => exact empty
  | cons entry rest ih =>
    apply ih
    · intro entry member
      exact different entry (List.mem_cons_of_mem _ member)
    · exact (accountMap_find?_insert_ne initial query entry.1 entry.2
        (Ne.symm (different entry List.mem_cons_self))).trans empty

/-- Map account values while preserving each address. This is the map used for transient reset. -/
def mapAccountValues (accounts : AccountMap) (transform : Account → Account) : AccountMap :=
  accounts.map (fun entry => (entry.1, transform entry.2))

/-- Account-value mapping changes only the value returned at each existing address. -/
theorem map_account_values_find (accounts : AccountMap) (transform : Account → Account)
    (query : AccountAddress) :
    (mapAccountValues accounts transform).find? query = (accounts.find? query).map transform := by
  have result :
      ((accounts.toList.map (fun entry => (entry.1, transform entry.2))).foldl
        (fun (result : AccountMap) entry => result.insert entry.1 entry.2) ∅).find? query =
      (accounts.find? query).map transform := by
    cases found : accounts.find? query with
    | none =>
      apply fold_accounts_find_none
      · intro entry member same
        obtain ⟨⟨owner, account⟩, original, equal⟩ := List.mem_map.mp member
        subst entry
        dsimp only at same
        subst owner
        have present : accounts.find? query = some account :=
          Batteries.RBMap.find?_some.mpr ⟨query, original, by simp [compare, compareOfLessAndEq]⟩
        rw [found] at present
        cases present
      · rfl
    | some value =>
      apply fold_accounts_find_some
      · intro entry member same
        obtain ⟨⟨owner, account⟩, original, equal⟩ := List.mem_map.mp member
        subst entry
        dsimp only at same ⊢
        subst owner
        have present : accounts.find? query = some account :=
          Batteries.RBMap.find?_some.mpr ⟨query, original, by simp [compare, compareOfLessAndEq]⟩
        have equal := Option.some.inj (present.symm.trans found)
        rw [equal]
      · obtain ⟨owner, member, comparison⟩ := Batteries.RBMap.find?_some_mem_toList found
        have equal : query = owner := by
          by_contra different
          exact accountAddress_compare_ne_eq_of_ne different comparison
        subst owner
        exact .inr (List.mem_map.mpr ⟨(query, value), member, rfl⟩)
  unfold mapAccountValues Batteries.RBSet.map
  rw [Batteries.RBSet.foldl_eq_foldl_toList]
  simpa only [List.foldl_map] using result

end Rollup.EVM
