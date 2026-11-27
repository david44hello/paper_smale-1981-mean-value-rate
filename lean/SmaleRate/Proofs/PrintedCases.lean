/-
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
import SmaleRate.Proofs.FiniteBoxSoundness

noncomputable section
namespace SmaleRate.Proofs
open Set Filter

section DLMF
variable (hdlmf : ∀ modulus ∈ Ioo 0 1,
  Real.log ((1 + Real.sqrt (complement modulus))^2 / modulus) < mu modulus ∧
    mu modulus < Real.log (2 * (1 + complement modulus) / modulus))
include hdlmf

theorem beta_gt_simple_exponential (degree : ℕ) (hdegree : 2 ≤ degree)
    (length : ℝ) (hlength : 0 < length) :
    Real.exp ((1-1/(degree : ℝ))*length) < beta degree length := by
  have hmem := radius_mem degree hdegree length hlength
  have hupper := mu_log_upper_of_upper_dlmf _ hmem (hdlmf _ hmem).2
  rw [Real.log_div (by norm_num) (ne_of_gt hmem.1), radius, Real.log_exp] at hupper
  change mu (radius degree length) < Real.log 4 - -length/(degree : ℝ) at hupper
  simp only [neg_div, sub_neg_eq_add] at hupper
  have hid : (1-1/(degree : ℝ))*length-Real.log 4 =
      length-(Real.log 4+length/(degree : ℝ)) := by ring
  have hstrict : Real.exp (((1-1/(degree : ℝ))*length)-Real.log 4) <
      Real.exp (length-mu (radius degree length)) := by
    apply Real.exp_lt_exp.mpr
    rw [hid]
    linarith
  rw [Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 4)] at hstrict
  unfold beta
  linarith

theorem prop_case_a_proved (degree : ℕ) (hdegree : 8 ≤ degree)
    (length : ℝ) (hlength : 2 ≤ length) :
    4 < Real.exp ((1-1/(degree : ℝ))*length) ∧
      Real.exp ((1-1/(degree : ℝ))*length) < beta degree length := by
  have hd : (8 : ℝ) ≤ degree := by exact_mod_cast hdegree
  have hdpos : 0 < (degree : ℝ) := by linarith
  have hinv : 1/(degree : ℝ) ≤ 1/8 := by
    apply (div_le_div_iff₀ hdpos (by norm_num : (0 : ℝ) < 8)).2
    linarith
  have hlog : Real.log 4 < (7/4 : ℝ) := by
    rw [Real.log_four_eq]
    linarith [Real.log_two_lt_d9]
  have hexponent : (7/4 : ℝ) ≤ (1-1/(degree : ℝ))*length := by
    nlinarith [mul_nonneg (show 0 ≤ length-2 by linarith)
      (show 0 ≤ 1-1/(degree : ℝ) by linarith)]
  refine ⟨?_, beta_gt_simple_exponential hdlmf degree (by omega) length (by linarith)⟩
  rw [← Real.exp_log (by norm_num : (0 : ℝ) < 4)]
  exact Real.exp_lt_exp.mpr (hlog.trans_le hexponent)

theorem prop_case_b_proved (degree : ℕ) (hdegree : 8 ≤ degree) (length : ℝ)
    (hlower : Real.pi^2/(2*ell degree) ≤ length) (hupper : length < 2) :
    4 < beta degree length := by
  have hell : 0 < ell degree := by linarith [ell_gt_one degree hdegree]
  have hpi : 0 < Real.pi^2 := sq_pos_of_pos Real.pi_pos
  have hlpos : 0 < length := (div_pos hpi (by positivity)).trans_le hlower
  have hdelta := prop_delta_bound_from_dlmf hdlmf degree hdegree length ⟨hlpos,hupper⟩
  have hdivide : Real.pi^2/delta degree length < Real.pi^2/(2*ell degree) := by
    apply (div_lt_div_iff₀ hdelta.1 (by positivity : 0 < 2*ell degree)).2
    nlinarith [mul_pos hpi (sub_pos.mpr (delta_gt_two_ell degree hdegree length ⟨hlpos,hupper⟩))]
  have hmu : mu (radius degree length) < length := hdelta.2.2.trans (hdivide.trans_le hlower)
  have hexp := Real.one_lt_exp_iff.mpr (sub_pos.mpr hmu)
  unfold beta
  linarith

theorem prop_case_c_proved (degree : ℕ) (hdegree : 8 ≤ degree) (length : ℝ)
    (hlength : length ∈ Ioo 0 (min 2 (Real.pi^2/(2*ell degree)))) :
    uniformLower degree < beta degree length := by
  exact (uniform_lower_le_simple degree hdegree).trans_lt
    (beta_simple_lower_small_from_dlmf hdlmf degree hdegree length
      ⟨hlength.1, hlength.2.trans_le (min_le_left _ _)⟩)

theorem range_interval_lower_proved (degree : ℕ) (hdegree : 2 ≤ degree)
    (lower upper length : ℝ) (hlower : 0 ≤ lower)
    (horder : lower < length) (hupper : length ≤ upper) :
    4*Real.exp lower*Real.exp (-mu (radius degree upper)) ≤ beta degree length := by
  have hlpos : 0 < length := hlower.trans_lt horder
  have hdpos : 0 < (degree : ℝ) := by exact_mod_cast (show 0 < degree by omega)
  have hradius : radius degree upper ≤ radius degree length := by
    unfold radius
    exact Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (neg_le_neg hupper) hdpos.le)
  have hpositive : ∀ modulus ∈ Ioo 0 1, 0 < mu modulus :=
    fun modulus hmodulus => mu_positive_of_lower_dlmf modulus hmodulus (hdlmf modulus hmodulus).1
  have hmu := (mu_decreasing_of_positive hpositive).antitoneOn
    (radius_mem degree hdegree upper (hlpos.trans_le hupper))
    (radius_mem degree hdegree length hlpos) hradius
  unfold beta
  rw [Real.exp_sub, div_eq_mul_inv, ← Real.exp_neg, ← mul_assoc]
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr horder.le) (by norm_num)
  · exact Real.exp_le_exp.mpr (neg_le_neg hmu)
  · positivity
  · positivity

theorem range_tail_proved (degree : ℕ) (hdegree : degree = 7 ∨ degree = 8)
    (length : ℝ) (hlength : 1 ≤ length) :
    (235/100 : ℝ) < Real.exp (6/7) ∧ Real.exp (6/7) ≤ beta degree length := by
  refine ⟨?_, beta_tail_seven_eight hdlmf degree hdegree length hlength⟩
  have hbound := exp_lower_eight (6/7) (by norm_num)
  norm_num [Finset.sum_range_succ] at hbound
  linarith

end DLMF
end SmaleRate.Proofs
