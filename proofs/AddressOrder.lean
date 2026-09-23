import Ethereum.Theory.AccountLocality

open Ethereum

namespace Rollup.EVM

/-- Account-address comparison inherits transitivity from natural-number comparison. -/
instance addressTransCmp : Std.TransCmp (compare : AccountAddress → AccountAddress → Ordering) where
  eq_swap := by
    intro a b
    exact Std.OrientedCmp.eq_swap (cmp := (compare : Nat → Nat → Ordering))
  isLE_trans := by
    intro a b c first second
    exact Std.TransCmp.isLE_trans (cmp := (compare : Nat → Nat → Ordering)) first second

end Rollup.EVM
