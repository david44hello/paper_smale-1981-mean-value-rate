/-
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
import SmaleRate.Defs.AnalyticBackground

namespace SmaleRate.Proofs
open Set

inductive BoxTree where
  | leaf (lower : ℚ)
  | split (left right : BoxTree)

def treeBoxes : BoxTree → ℚ → ℚ → List CertifiedBoxData
  | .leaf lower, left, right => [{left := left, right := right, lower := lower}]
  | .split first second, left, right =>
      treeBoxes first left ((left+right)/2) ++ treeBoxes second ((left+right)/2) right

def treeAll (predicate : CertifiedBoxData → Prop) : BoxTree → ℚ → ℚ → Prop
  | .leaf lower, left, right => predicate {left := left, right := right, lower := lower}
  | .split first second, left, right =>
      treeAll predicate first left ((left+right)/2) ∧ treeAll predicate second ((left+right)/2) right

theorem tree_boxes_all (predicate : CertifiedBoxData → Prop) (tree : BoxTree) (left right : ℚ) :
    (∀ box ∈ treeBoxes tree left right, predicate box) ↔ treeAll predicate tree left right := by
  induction tree generalizing left right with
  | leaf lower => simp [treeBoxes, treeAll]
  | split first second ihFirst ihSecond =>
    simp only [treeBoxes, List.forall_mem_append, treeAll, ihFirst, ihSecond]

theorem tree_boxes_not_nil (tree : BoxTree) (left right : ℚ) : treeBoxes tree left right ≠ [] := by
  induction tree generalizing left right with
  | leaf lower => simp [treeBoxes]
  | split first second ihFirst ihSecond =>
    intro hnil
    change treeBoxes first left ((left+right)/2) ++ treeBoxes second ((left+right)/2) right = [] at hnil
    exact ihFirst left ((left+right)/2) (List.append_eq_nil_iff.mp hnil).1

theorem tree_boxes_valid (tree : BoxTree) (left right : ℚ)
    (hleft : 0 ≤ left) (horder : left < right) (hright : right ≤ 1) :
    ∀ box ∈ treeBoxes tree left right, ValidBox box := by
  induction tree generalizing left right with
  | leaf lower =>
    intro box hbox
    simp only [treeBoxes, List.mem_singleton] at hbox
    subst box
    exact ⟨hleft, horder, hright⟩
  | split first second ihFirst ihSecond =>
    intro box hbox
    have hmidLeft : left < (left+right)/2 := by linarith
    have hmidRight : (left+right)/2 < right := by linarith
    change box ∈ treeBoxes first left ((left+right)/2) ++ treeBoxes second ((left+right)/2) right at hbox
    rcases List.mem_append.mp hbox with hbox | hbox
    · exact ihFirst left ((left+right)/2) hleft hmidLeft (hmidRight.le.trans hright) box hbox
    · exact ihSecond ((left+right)/2) right (hleft.trans hmidLeft.le) hmidRight hright box hbox

theorem tree_boxes_cover (tree : BoxTree) (left right : ℚ) (length : ℝ)
    (hleft : (left : ℝ) < length) (hright : length ≤ (right : ℝ)) :
    ∃ box ∈ treeBoxes tree left right, (box.left : ℝ) < length ∧ length ≤ (box.right : ℝ) := by
  induction tree generalizing left right with
  | leaf lower =>
    exact ⟨{left := left, right := right, lower := lower}, by simp [treeBoxes], hleft, hright⟩
  | split first second ihFirst ihSecond =>
    by_cases hsmall : length ≤ (((left+right)/2 : ℚ) : ℝ)
    · obtain ⟨box, hbox, hb⟩ := ihFirst left ((left+right)/2) hleft hsmall
      exact ⟨box, List.mem_append.mpr (Or.inl hbox), hb⟩
    · obtain ⟨box, hbox, hb⟩ := ihSecond ((left+right)/2) right (lt_of_not_ge hsmall) hright
      exact ⟨box, List.mem_append.mpr (Or.inr hbox), hb⟩

theorem dyadic_unit_cover (tree : BoxTree) :
    treeBoxes tree 0 1 ≠ [] ∧ CoversUnit (treeBoxes tree 0 1) ∧
      ∀ box ∈ treeBoxes tree 0 1, ValidBox box := by
  refine ⟨tree_boxes_not_nil tree 0 1, ?_, tree_boxes_valid tree 0 1 (by norm_num) (by norm_num) (by norm_num)⟩
  intro length hlength
  exact tree_boxes_cover tree 0 1 length (by simpa using hlength.1) (by simpa using hlength.2)

end SmaleRate.Proofs

#check SmaleRate.Proofs.dyadic_unit_cover
#print axioms SmaleRate.Proofs.dyadic_unit_cover
#check SmaleRate.Proofs.tree_boxes_all
#print axioms SmaleRate.Proofs.tree_boxes_all
