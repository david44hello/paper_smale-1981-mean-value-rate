/-
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
import SmaleRate.Defs.AnalyticBackground
import SmaleRate.Proofs.MuLimits

noncomputable section
namespace SmaleRate.Proofs
open Set Filter

section DLMF
variable (hdlmf : ∀ modulus ∈ Ioo 0 1,
  Real.log ((1 + Real.sqrt (complement modulus))^2 / modulus) < mu modulus ∧
    mu modulus < Real.log (2 * (1 + complement modulus) / modulus))
include hdlmf

theorem beta_lower_on_box (degree : ℕ) (hdegree : 2 ≤ degree) (box : CertifiedBoxData)
    (hvalid : ValidBox box) (hbound : BoxEndpointBound degree box)
    (length : ℝ) (hlength : 0 < length)
    (hleft : (box.left : ℝ) < length) (hright : length ≤ (box.right : ℝ)) :
    (box.lower : ℝ) ≤ beta degree length := by
  have hdpos : 0 < (degree : ℝ) := by exact_mod_cast (show 0 < degree by omega)
  have hrightpos : 0 < (box.right : ℝ) := hlength.trans_le hright
  have hradius : radius degree (box.right : ℝ) ≤ radius degree length := by
    unfold radius
    apply Real.exp_le_exp.mpr
    exact div_le_div_of_nonneg_right (neg_le_neg hright) hdpos.le
  have hpositive : ∀ modulus ∈ Ioo 0 1, 0 < mu modulus :=
    fun modulus hmodulus => mu_positive_of_lower_dlmf modulus hmodulus (hdlmf modulus hmodulus).1
  have horder := (mu_decreasing_of_positive hpositive).antitoneOn
    (radius_mem degree hdegree (box.right : ℝ) hrightpos)
    (radius_mem degree hdegree length hlength) hradius
  unfold BoxEndpointBound at hbound
  unfold beta
  rw [Real.exp_sub, div_eq_mul_inv, ← Real.exp_neg]
  rw [← mul_assoc]
  apply hbound.trans
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hleft.le) (by norm_num)
  · exact Real.exp_le_exp.mpr (neg_le_neg horder)
  · positivity
  · positivity

theorem beta_tail_seven_eight (degree : ℕ) (hdegree : degree = 7 ∨ degree = 8)
    (length : ℝ) (hlength : 1 ≤ length) : Real.exp (6/7 : ℝ) ≤ beta degree length := by
  have hdegree2 : 2 ≤ degree := by rcases hdegree with rfl | rfl <;> omega
  have hdpos : 0 < (degree : ℝ) := by exact_mod_cast (show 0 < degree by omega)
  have hlengthpos : 0 < length := by linarith
  have hmem := radius_mem degree hdegree2 length hlengthpos
  have hupper := mu_log_upper_of_upper_dlmf _ hmem (hdlmf _ hmem).2
  have hlog : Real.log (4 / radius degree length) = Real.log 4 + length / (degree : ℝ) := by
    rw [Real.log_div (by norm_num) (ne_of_gt hmem.1), radius, Real.log_exp]
    ring
  rw [hlog] at hupper
  have hquotient : (6/7 : ℝ) ≤ length - length / (degree : ℝ) := by
    rcases hdegree with rfl | rfl <;> norm_num <;> linarith
  unfold beta
  have hstrict : 4 * Real.exp (length - (Real.log 4 + length / (degree : ℝ))) <
      4 * Real.exp (length - mu (radius degree length)) := by
    apply mul_lt_mul_of_pos_left _ (by norm_num)
    exact Real.exp_lt_exp.mpr (by linarith)
  have hid : 4 * Real.exp (length - (Real.log 4 + length / (degree : ℝ))) =
      Real.exp (length - length / (degree : ℝ)) := by
    rw [show length-(Real.log 4+length/(degree : ℝ)) =
      (length-length/(degree : ℝ))-Real.log 4 by ring, Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 4)]
    ring
  rw [hid] at hstrict
  exact (Real.exp_le_exp.mpr hquotient).trans hstrict.le

theorem finite_box_soundness_from_dlmf (degree : ℕ) (hdegree : degree = 7 ∨ degree = 8)
    (boxes : List CertifiedBoxData) (hnonempty : boxes ≠ [])
    (hvalid : ∀ box ∈ boxes, ValidBox box) (hcover : CoversUnit boxes)
    (hendpoint : ∀ box ∈ boxes, BoxEndpointBound degree box)
    (cutoff : ℝ) (hcutoff : ∀ box ∈ boxes, cutoff < (box.lower : ℝ))
    (htail : cutoff < Real.exp (6/7)) : cutoff < bestBound degree := by
  classical
  let values : Finset ℝ := boxes.toFinset.image (fun box => (box.lower : ℝ))
  have hvalues : values.Nonempty := by
    cases boxes with
    | nil => exact False.elim (hnonempty rfl)
    | cons box rest => exact ⟨(box.lower : ℝ), by simp [values]⟩
  let minimum : ℝ := values.min' hvalues
  have hminimum_gt : cutoff < minimum := by
    have hmem := Finset.min'_mem values hvalues
    obtain ⟨box, hbox, heq⟩ := Finset.mem_image.mp hmem
    change cutoff < values.min' hvalues
    rw [← heq]
    exact hcutoff box (List.mem_toFinset.mp hbox)
  have hminimum_le : ∀ box ∈ boxes, minimum ≤ (box.lower : ℝ) := by
    intro box hbox
    exact Finset.min'_le values _ (Finset.mem_image.mpr ⟨box, List.mem_toFinset.mpr hbox, rfl⟩)
  have huniform : ∀ length : ℝ, 0 < length → min minimum (Real.exp (6/7 : ℝ)) ≤ beta degree length := by
    intro length hlength
    by_cases hsmall : length ≤ 1
    · obtain ⟨box, hbox, hleft, hright⟩ := hcover length ⟨hlength, hsmall⟩
      have hdegree2 : 2 ≤ degree := by rcases hdegree with rfl | rfl <;> omega
      exact (min_le_left _ _).trans ((hminimum_le box hbox).trans
        (beta_lower_on_box hdlmf degree hdegree2 box (hvalid box hbox) (hendpoint box hbox)
          length hlength hleft hright))
    · exact (min_le_right _ _).trans (beta_tail_seven_eight hdlmf degree hdegree length (by linarith))
  exact (lt_min hminimum_gt htail).trans_le (best_bound_lower_of_beta degree _ huniform)

end DLMF
end SmaleRate.Proofs
