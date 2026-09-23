-- Tree deletion lemmas adapted from pinned EVMLean, Ethereum/Theory/StorageExtensionality.lean.
import proofs.AddressOrder

open Ethereum Ethereum.EVM

namespace Rollup.EVM

private theorem rbNode_suffix_eq {α} {b' c' b c d : List α} {z y : α}
    (ih : b' ++ z :: c' = b ++ c) :
    b' ++ z :: (c' ++ y :: d) = b ++ (c ++ y :: d) := by
  calc
    b' ++ z :: (c' ++ y :: d) = (b' ++ z :: c') ++ y :: d := by
      simp [List.append_assoc]
    _ = (b ++ c) ++ y :: d := by rw [ih]
    _ = b ++ (c ++ y :: d) := by simp [List.append_assoc]

private theorem rbNode_append_toList {α} : ∀ (l r : Batteries.RBNode α),
    (l.append r).toList = l.toList ++ r.toList
  | .nil, r => by simp [Batteries.RBNode.append]
  | .node c a x b, .nil => by cases c <;> simp [Batteries.RBNode.append]
  | .node .red a x b, .node .black c y d => by
      simp only [Batteries.RBNode.append, Batteries.RBNode.toList_node]
      rw [rbNode_append_toList]
      simp [List.append_assoc]
  | .node .black a x b, .node .red c y d => by
      simp only [Batteries.RBNode.append, Batteries.RBNode.toList_node]
      rw [rbNode_append_toList]
      simp [List.append_assoc]
  | .node .red a x b, .node .red c y d => by
      simp only [Batteries.RBNode.append]
      cases h : Batteries.RBNode.append b c with
      | nil =>
          have hih := rbNode_append_toList b c
          rw [h] at hih
          simp at hih
          simp [hih, List.append_assoc]
      | node col b' z c' =>
          have ih : b'.toList ++ z :: c'.toList = b.toList ++ c.toList := by
            have hih := rbNode_append_toList b c
            rw [h] at hih
            simpa using hih
          cases col <;> simp only [Batteries.RBNode.toList_node]
          · have hs := rbNode_suffix_eq (y := y) (d := d.toList) ih
            simpa [List.append_assoc] using congrArg (fun t => a.toList ++ x :: t) hs
          · simp [rbNode_suffix_eq (y := y) (d := d.toList) ih, List.append_assoc]
  | .node .black a x b, .node .black c y d => by
      simp only [Batteries.RBNode.append]
      cases h : Batteries.RBNode.append b c with
      | nil =>
          have hih := rbNode_append_toList b c
          rw [h] at hih
          simp at hih
          simp [hih, List.append_assoc]
      | node col b' z c' =>
          have ih : b'.toList ++ z :: c'.toList = b.toList ++ c.toList := by
            have hih := rbNode_append_toList b c
            rw [h] at hih
            simpa using hih
          cases col <;> simp only [Batteries.RBNode.toList_node]
          · have hs := rbNode_suffix_eq (y := y) (d := d.toList) ih
            simpa [List.append_assoc] using congrArg (fun t => a.toList ++ x :: t) hs
          · rw [Batteries.RBNode.balLeft_toList]
            simp [rbNode_suffix_eq (y := y) (d := d.toList) ih, List.append_assoc]
termination_by l r => l.size + r.size

private theorem rbNode_filter_all_bool {α} {t : Batteries.RBNode α} {p : α → Bool}
    (h : ∀ x, x ∈ t → p x = true) : t.toList.filter p = t.toList := by
  apply List.filter_eq_self.2
  intro x hx
  exact h x (by simpa using hx)

private theorem rbNode_del_toList_filter {α} {cmp : α → α → Ordering} {cut : α → Ordering}
    [Std.TransCmp cmp] [Batteries.RBNode.IsStrictCut cmp cut] :
    ∀ (t : Batteries.RBNode α), Batteries.RBNode.Ordered cmp t →
      (t.del cut).toList = t.toList.filter (fun x => cut x != .eq)
  | .nil, _ => by simp [Batteries.RBNode.del]
  | .node _ a y b, ht => by
      rcases ht with ⟨hay, hyb, ha, hb⟩
      unfold Batteries.RBNode.del
      cases hy : cut y
      · have hbfilter : b.toList.filter (fun x => cut x != .eq) = b.toList := by
          apply rbNode_filter_all_bool
          intro z hz
          have hzlt : cut z = .lt :=
            Batteries.RBNode.IsCut.lt_trans (Batteries.RBNode.All_def.1 hyb z hz).1 hy
          simp [hzlt]
        cases a.isBlack <;>
          simp [hy, rbNode_del_toList_filter a ha, Batteries.RBNode.balLeft_toList,
            hbfilter]
      · have hafilter : a.toList.filter (fun x => cut x != .eq) = a.toList := by
          apply rbNode_filter_all_bool
          intro z hz
          have hzy : cmp z y = .lt := (Batteries.RBNode.All_def.1 hay z hz).1
          have hyz : cmp y z = .gt := Std.OrientedCmp.gt_iff_lt.2 hzy
          have hcut : cut z = .gt := by
            have htmp : cmp y z = cut z :=
              Batteries.RBNode.IsStrictCut.exact (cmp := cmp) (cut := cut) hy
            simpa [hyz] using htmp.symm
          simp [hcut]
        have hbfilter : b.toList.filter (fun x => cut x != .eq) = b.toList := by
          apply rbNode_filter_all_bool
          intro z hz
          have hyz : cmp y z = .lt := (Batteries.RBNode.All_def.1 hyb z hz).1
          have hcut : cut z = .lt := by
            have htmp : cmp y z = cut z :=
              Batteries.RBNode.IsStrictCut.exact (cmp := cmp) (cut := cut) hy
            simpa [hyz] using htmp.symm
          simp [hcut]
        simp [hy, rbNode_append_toList, hafilter, hbfilter]
      · have hafilter : a.toList.filter (fun x => cut x != .eq) = a.toList := by
          apply rbNode_filter_all_bool
          intro z hz
          have hzgt : cut z = .gt :=
            Batteries.RBNode.IsCut.gt_trans (Batteries.RBNode.All_def.1 hay z hz).1 hy
          simp [hzgt]
        cases b.isBlack <;>
          simp [hy, rbNode_del_toList_filter b hb, Batteries.RBNode.balRight_toList,
            hafilter]
termination_by t => t.size

theorem rbNode_erase_toList_filter {α} {cmp : α → α → Ordering}
    {cut : α → Ordering} [Std.TransCmp cmp] [Batteries.RBNode.IsStrictCut cmp cut]
    (t : Batteries.RBNode α) (ht : Batteries.RBNode.Ordered cmp t) :
    (t.erase cut).toList = t.toList.filter (fun x => cut x != .eq) := by
  simp [Batteries.RBNode.erase, rbNode_del_toList_filter t ht]

end Rollup.EVM
