namespace Rollup.EVM

/-- Check one array item by its index. -/
def arrayPredicateAt {α : Type} (table : Array α) (predicate : α → Bool) (index : Nat) : Bool :=
  match table[index]? with
  | some item => predicate item
  | none => false

end Rollup.EVM
