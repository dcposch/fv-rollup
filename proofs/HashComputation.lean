/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license.
Adapted from Lean 4.29.0 Lean/Meta/Tactic/Cbv/Main.lean.
Author: Wojciech Różowski.
-/
module
public meta import Lean
public meta import Lean.Meta.Tactic.Refl
meta import all Lean.Meta.Tactic.Cbv.Main
meta import all Lean.Meta.Sym.Simp.Main
public section
namespace Lean.Meta.Tactic.Cbv
open Lean.Meta.Sym.Simp
private meta def cbvLargeCore (m : MVarId) (inv : Bool := false) : MetaM (Option MVarId) := do
  Sym.SymM.run do
    let methods := {pre := cbvPre, post := cbvPost}
    let m ← Sym.preprocessMVar m
    let mType ← m.getType
    let some (_, lhs, rhs) := mType.eq? | return m
    let (toReduce, toCompare) := if inv then (rhs, lhs) else (lhs, rhs)
    let result ← SimpM.run' (Lean.Meta.Sym.Simp.simp toReduce) (methods := methods) (config := { maxSteps := 2000000 })
    match result with
    | .rfl _ =>
      unless (← isDefEq toReduce toCompare) do return m
      m.refl
      return .none
    | .step e' proof _ =>
      if (← isDefEq e' toCompare) then
        if inv then
          m.assign (← mkEqSymm proof)
        else
          m.assign proof
        return .none
      else
        if inv then
          let newGoalType ← mkEq toCompare e'
          let newGoal ← mkFreshExprMVar newGoalType
          let toAssign ← mkEqTrans newGoal proof
          m.assign toAssign
          return newGoal.mvarId!
        else
          let newGoalType ← mkEq e' toCompare
          let newGoal ← mkFreshExprMVar newGoalType
          let toAssign ← mkEqTrans proof newGoal
          m.assign toAssign
          return newGoal.mvarId!

end Lean.Meta.Tactic.Cbv
open Lean Elab Tactic in
elab "keccak_cbv" : tactic => withMainContext do
  liftMetaTactic fun goal => do
    match (← Lean.Meta.Tactic.Cbv.cbvLargeCore goal) with
    | none => return []
    | some rest => return [rest]
