import proofs.BoundaryErase

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- The pinned rollup is not an empty account under the transaction cleanup test. -/
theorem pinned_account_not_empty (accounts : AccountMap) (self : Address)
    (pinned : (accounts.findD self default).code = runtimeBytecode) :
    Ethereum.State.dead accounts self = false := by
  obtain ⟨account, found, code⟩ := pinned_account_present pinned
  have nonempty : runtimeBytecode.isEmpty = false := by decide +kernel
  simp only [Ethereum.State.dead, found, Option.option, Account.emptyAccount, code, nonempty]
  simp

/-- A set filter excludes an address where its predicate is false. -/
theorem address_filter_excludes (self : AccountAddress) (owners : Batteries.RBSet AccountAddress compare)
    (predicate : AccountAddress → Bool) (excluded : predicate self = false) :
    self ∉ owners.filter predicate := by
  have fold : ∀ (entries : List AccountAddress) (acc : Batteries.RBSet AccountAddress compare),
      self ∉ acc → self ∉ entries.foldl (fun result owner => bif predicate owner then result.insert owner else result) acc := by
    intro entries
    induction entries with
    | nil => intro acc absent; exact absent
    | cons owner rest ih =>
      intro acc absent
      simp only [List.foldl_cons]
      cases selected : predicate owner with
      | false => simpa only [selected, cond_false] using ih acc absent
      | true =>
        simp only [cond_true]
        apply ih
        intro member
        rcases (Batteries.RBSet.mem_insert (t := acc)).mp member with old | same
        · exact absent old
        · have different : owner ≠ self := by
            intro equality
            rw [equality, excluded] at selected
            cases selected
          exact accountAddress_compare_ne_eq_of_ne different same
  unfold Batteries.RBSet.filter
  rw [Batteries.RBSet.foldl_eq_foldl_toList]
  apply fold
  intro member
  obtain ⟨owner, member, _⟩ := Batteries.RBSet.mem_iff_mem_toList.mp member
  exact List.not_mem_nil member

/-- The exact dead-account filter used by transaction cleanup excludes the rollup. -/
theorem dead_accounts_exclude_rollup (self : Address) (accounts : AccountMap)
    (touched : Batteries.RBSet AccountAddress compare)
    (pinned : (accounts.findD self default).code = runtimeBytecode) :
    self ∉ touched.filter (Ethereum.State.dead accounts ·) :=
  address_filter_excludes self touched _ (pinned_account_not_empty accounts self pinned)

/-- Both transaction deletion passes preserve the rollup boundary. -/
theorem transaction_deletions_refine (self : Address) (accounts : AccountMap) (substate : Substate)
    (keys : AccessScope) (absent : self ∉ substate.selfDestructSet)
    (ready : BoundaryReady self accounts keys) (safe : Safe (boundaryModel self accounts keys)) :
    BoundaryRefines self keys accounts
      ((substate.touchedAccounts.filter (Ethereum.State.dead accounts ·)).foldl Batteries.RBMap.erase
        (substate.selfDestructSet.1.foldl Batteries.RBMap.erase accounts)) := by
  have first := boundary_erase_set_refines self substate.selfDestructSet accounts keys absent ready safe
  have second := boundary_erase_set_refines self
    (substate.touchedAccounts.filter (Ethereum.State.dead accounts ·)) _ keys
    (dead_accounts_exclude_rollup self accounts substate.touchedAccounts (BoundaryReady.pinned ready))
    first.1 first.2.1
  exact boundary_refines_trans first second

end Rollup.EVM
