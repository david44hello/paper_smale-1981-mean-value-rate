/-
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
import SmaleRate.Proofs.Elementary

noncomputable section
namespace SmaleRate.Proofs
open Set Filter

theorem log_twenty_one_gt_three_zero_four : (304/100 : ℝ) < Real.log 21 := by
  apply (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 21)).2
  have hsmall := Real.exp_bound_div_one_sub_of_interval (x := (4/100 : ℝ)) (by norm_num) (by norm_num)
  have he : Real.exp 1 < (2719/1000 : ℝ) := by linarith [Real.exp_one_lt_d9]
  have hthree : Real.exp (3 : ℝ) < (2719/1000 : ℝ)^3 := by
    calc
      Real.exp (3 : ℝ) = (Real.exp 1)^3 := by rw [← Real.exp_nat_mul]; norm_num
      _ < (2719/1000 : ℝ)^3 := by gcongr
  calc
    Real.exp (304/100 : ℝ) = Real.exp 3*Real.exp (4/100) := by rw [← Real.exp_add]; congr 1; norm_num
    _ ≤ (2719/1000 : ℝ)^3*(25/24) := by
      apply mul_le_mul hthree.le (by norm_num at hsmall ⊢; exact hsmall) (Real.exp_nonneg _) (by positivity)
    _ < 21 := by norm_num

theorem log_tail_cap : Real.log (2432/25 : ℝ) < (461/100 : ℝ) := by
  apply (Real.log_lt_iff_lt_exp (by norm_num)).2
  calc
    (2432/25 : ℝ) < (2718/1000 : ℝ)^4*(184/100) := by norm_num
    _ ≤ Real.exp (4 : ℕ)*Real.exp (61/100) :=
      mul_le_mul (exp_integer_lower 4) exp_sixty_one_hundredths_lower (by norm_num) (Real.exp_nonneg _)
    _ = Real.exp (461/100) := by rw [← Real.exp_add]; congr 1; norm_num

theorem log_scaled_tail (value : ℝ) (hvalue : (304/100 : ℝ) ≤ value) :
    Real.log (32*value) < (152/100)*value := by
  have hvpos : 0 < value := by linarith
  have hlog := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < value/(76/25))
  have hid : Real.log (32*value) = Real.log (2432/25 : ℝ)+Real.log (value/(76/25)) := by
    rw [← Real.log_mul (by norm_num) (by positivity : value/(76/25) ≠ 0)]
    congr 1
    ring
  rw [hid]
  linarith [log_tail_cap]

theorem tail_log_ratio_decreasing_proved :
    StrictAntiOn (fun value : ℝ => Real.log (32*value)/value) (Ici 1) := by
  have hderivative (value : ℝ) (hv : 1 ≤ value) :
      HasDerivAt (fun value : ℝ => Real.log (32*value)/value)
        ((1-Real.log (32*value))/value^2) value := by
    have hvpos : 0 < value := by linarith
    have hvne := ne_of_gt hvpos
    have hlogder : HasDerivAt (fun value : ℝ => Real.log (32*value)) (1/value) value := by
      convert (Real.hasDerivAt_log (by positivity : (32*value : ℝ) ≠ 0)).comp value
        ((hasDerivAt_id value).const_mul 32) using 1 <;>
        (try simp only [id_eq, Function.comp_def]) <;> field_simp [hvne] <;> ring
    convert hlogder.div (hasDerivAt_id value) hvne using 1
    · funext argument
      simp only [Pi.div_apply, id_eq]
    · simp only [id_eq]
      field_simp [hvne]
      <;> ring
  apply strictAntiOn_of_deriv_neg (convex_Ici 1)
  · intro value hv
    exact (hderivative value hv).continuousAt.continuousWithinAt
  · intro value hv
    have hvalue : 1 ≤ value := interior_subset hv
    have hvpos : 0 < value := by linarith
    rw [(hderivative value hvalue).deriv]
    apply div_neg_of_neg_of_pos _ (sq_pos_of_pos hvpos)
    have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 32)
      (by linarith : (32 : ℝ) ≤ 32*value)
    have hlog32 : Real.log (32 : ℝ) = 5*Real.log 2 := by
      rw [show (32 : ℝ) = (2 : ℝ)^5 by norm_num, Real.log_pow]; norm_num
    rw [hlog32] at hlog
    linarith [Real.log_two_gt_d9]

theorem tail_numerical_endpoints_proved :
    Real.log (32*Real.log 21)/Real.log 21 < (152/100 : ℝ) ∧
      -Real.log (1-(42/10000 : ℝ)) < 5/1000 := by
  constructor
  · apply (div_lt_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 21))).2
    exact log_scaled_tail _ log_twenty_one_gt_three_zero_four.le
  · exact (neg_log_one_sub_le (42/10000) (by norm_num) (by norm_num)).trans_lt (by norm_num)

theorem tail_constants_first_four (degree : ℕ) (hdegree : 21 ≤ degree) :
    (304/100 : ℝ) < ell degree ∧ Real.log (32*ell degree) ≤ (152/100)*ell degree ∧
    Lchoice degree/degree < 42/10000 ∧
    -Real.log (1-Lchoice degree/degree) < (2/1000)*ell degree := by
  have hd : (21 : ℝ) ≤ degree := by exact_mod_cast hdegree
  have hdpos : 0 < (degree : ℝ) := by linarith
  have hell : (304/100 : ℝ) < ell degree :=
    log_twenty_one_gt_three_zero_four.trans_le (Real.log_le_log (by norm_num) hd)
  have hepos : 0 < ell degree := by linarith
  have hlog := (log_scaled_tail _ hell.le).le
  have hratio : Lchoice degree/(degree : ℝ) < (42/10000 : ℝ) := by
    have hprod : (4*(304/100 : ℝ)*21) ≤ 4*ell degree*(degree : ℝ) := by
      nlinarith [mul_nonneg (by linarith : 0 ≤ ell degree-304/100) (by linarith : 0 ≤ (degree : ℝ)-21)]
    have hrecip := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4*(304/100)*21) hprod
    unfold Lchoice
    rw [div_div]
    exact hrecip.trans_lt (by norm_num)
  have hlogratio : -Real.log (1-Lchoice degree/(degree : ℝ)) < 5/1000 := by
    have hmono : Real.log (1-(42/10000 : ℝ)) < Real.log (1-Lchoice degree/(degree : ℝ)) :=
      Real.log_lt_log (by norm_num) (by linarith)
    linarith [tail_numerical_endpoints_proved.2]
  exact ⟨hell, hlog, hratio, hlogratio.trans (by linarith)⟩

theorem tail_lambda_upper_proved (degree : ℕ) (hdegree : 21 ≤ degree) :
    lambda degree (Lchoice degree) < (253/100)*ell degree := by
  have h := tail_constants_first_four degree hdegree
  have hepos : 0 < ell degree := by linarith [h.1]
  rw [lambda_chosen_identity degree (by omega)]
  linarith [h.2.1, h.2.2.2]

theorem tail_constants_proved (degree : ℕ) (hdegree : 21 ≤ degree) :
    (304/100 : ℝ) < ell degree ∧ Real.log (32*ell degree) ≤ (152/100)*ell degree ∧
    Lchoice degree/degree < 42/10000 ∧
    -Real.log (1-Lchoice degree/degree) < (2/1000)*ell degree ∧
    (195/100)/ell degree < Real.pi^2/(2*lambda degree (Lchoice degree)) := by
  have h := tail_constants_first_four degree hdegree
  have hepos : 0 < ell degree := by linarith [h.1]
  have hlambdapos := (log_complement_le_half_lambda degree (by omega) (Lchoice degree)
    (chosen_length_bounds degree (by omega))).1
  have hlambda := tail_lambda_upper_proved degree hdegree
  have hpi : (195/100 : ℝ)*(506/100) < Real.pi^2 := by nlinarith [Real.pi_gt_d4, Real.pi_pos]
  have hscaled := mul_lt_mul_of_pos_right hpi hepos
  refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, ?_⟩
  apply (div_lt_div_iff₀ hepos (by positivity : (0 : ℝ) < 2*lambda degree (Lchoice degree))).2
  nlinarith

end SmaleRate.Proofs

#check SmaleRate.Proofs.tail_log_ratio_decreasing_proved
#print axioms SmaleRate.Proofs.tail_log_ratio_decreasing_proved
#check SmaleRate.Proofs.tail_numerical_endpoints_proved
#print axioms SmaleRate.Proofs.tail_numerical_endpoints_proved
#check SmaleRate.Proofs.tail_lambda_upper_proved
#print axioms SmaleRate.Proofs.tail_lambda_upper_proved
#check SmaleRate.Proofs.tail_constants_proved
#print axioms SmaleRate.Proofs.tail_constants_proved
