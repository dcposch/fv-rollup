import semantics.ExecutionTree

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- The actual call guard makes a child use less of the remaining depth budget. -/
theorem child_call_remaining {jumps : Array UInt256} {before child : Ethereum.State}
    (entered : ChildCallEntry jumps before child) :
    1024 - child.executionEnv.depth.val < 1024 - before.executionEnv.depth.val := by
  cases entered with
  | entered instruction precheck arguments enabled selected =>
    have bounded : before.executionEnv.depth.val < 1024 := enabled.2
    change 1024 - (before.executionEnv.depth + 1).val < 1024 - before.executionEnv.depth.val
    rw [Fin.val_add_eq_of_add_lt (by change before.executionEnv.depth.val + 1 < 1025; omega)]
    change 1024 - (before.executionEnv.depth.val + 1) < 1024 - before.executionEnv.depth.val
    omega

/-- The actual creation guard makes initialization use less of the depth budget. -/
theorem child_creation_remaining {jumps : Array UInt256} {before child : Ethereum.State}
    (entered : ChildCreationEntry jumps before child) :
    1024 - child.executionEnv.depth.val < 1024 - before.executionEnv.depth.val := by
  cases entered with
  | entered instruction precheck arguments nonce allowed =>
    have bounded : before.executionEnv.depth.val < 1024 := allowed.2.1
    change 1024 - (before.executionEnv.depth.val + 1) < 1024 - before.executionEnv.depth.val
    omega

end Rollup.EVM
