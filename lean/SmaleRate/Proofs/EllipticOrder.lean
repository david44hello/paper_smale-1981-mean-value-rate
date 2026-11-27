/-
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
import SmaleRate.Proofs.Elementary

noncomputable section
namespace SmaleRate.Proofs
open Set MeasureTheory

theorem ellipticK_nonneg (modulus : ℝ) : 0 ≤ ellipticK modulus := by
  exact intervalIntegral.integral_nonneg_of_forall (by norm_num)
    (fun param => one_div_nonneg.mpr (Real.sqrt_nonneg _))

theorem ellipticK_positive_of_mu_positive (modulus : ℝ) (hmu : 0 < mu modulus) :
    0 < ellipticK modulus := by
  have hne : ellipticK modulus ≠ 0 := by
    intro hzero
    have hzero_mu : mu modulus = 0 := by simp [mu, hzero]
    linarith
  exact lt_of_le_of_ne (ellipticK_nonneg modulus) hne.symm

theorem elliptic_integrable_of_mu_positive (modulus : ℝ) (hmu : 0 < mu modulus) :
    IntervalIntegrable (fun param : ℝ =>
      1 / Real.sqrt ((1-param^2)*(1-modulus^2*param^2))) volume 0 1 := by
  exact intervalIntegral.intervalIntegrable_of_integral_ne_zero
    (ne_of_gt (ellipticK_positive_of_mu_positive modulus hmu))

theorem elliptic_integrand_strict (lower upper param : ℝ)
    (hlower : lower ∈ Ioo 0 1) (hupper : upper ∈ Ioo 0 1)
    (horder : lower < upper) (hparam : param ∈ Ioo 0 1) :
    1 / Real.sqrt ((1-param^2)*(1-lower^2*param^2)) <
      1 / Real.sqrt ((1-param^2)*(1-upper^2*param^2)) := by
  have hparam_sq : param^2 < 1 := by nlinarith [hparam.1, hparam.2]
  have hupper_sq : upper^2 < 1 := by nlinarith [hupper.1, hupper.2]
  have hupper_arg : 0 < (1-param^2)*(1-upper^2*param^2) := by
    apply mul_pos (by linarith)
    nlinarith [mul_pos (by linarith : 0 < 1-upper^2) (sq_pos_of_pos hparam.1)]
  have hsq_order : lower^2 < upper^2 := by nlinarith [hlower.1, horder]
  have harg_order : (1-param^2)*(1-upper^2*param^2) <
      (1-param^2)*(1-lower^2*param^2) := by
    apply mul_lt_mul_of_pos_left _ (by linarith)
    nlinarith [mul_pos (sub_pos.mpr hsq_order) (sq_pos_of_pos hparam.1)]
  exact one_div_lt_one_div_of_lt (Real.sqrt_pos.mpr hupper_arg)
    (Real.sqrt_lt_sqrt hupper_arg.le harg_order)

theorem elliptic_increasing_of_mu_positive
    (hmu : ∀ modulus ∈ Ioo 0 1, 0 < mu modulus) : StrictMonoOn ellipticK (Ioo 0 1) := by
  intro lower hlower upper hupper horder
  have hfirst := elliptic_integrable_of_mu_positive lower (hmu lower hlower)
  have hsecond := elliptic_integrable_of_mu_positive upper (hmu upper hupper)
  have hpositive := intervalIntegral.intervalIntegral_pos_of_pos_on (hsecond.sub hfirst)
    (fun param hparam => sub_pos.mpr (elliptic_integrand_strict lower upper param hlower hupper horder hparam))
    (by norm_num : (0 : ℝ) < 1)
  rw [intervalIntegral.integral_sub hsecond hfirst] at hpositive
  exact sub_pos.mp hpositive

theorem mu_decreasing_of_positive (hmu : ∀ modulus ∈ Ioo 0 1, 0 < mu modulus) :
    StrictAntiOn mu (Ioo 0 1) := by
  intro lower hlower upper hupper horder
  have hcomp_lower := complement_mem lower hlower
  have hcomp_upper := complement_mem upper hupper
  have hcomp_order : complement upper < complement lower := by
    unfold complement
    apply Real.sqrt_lt_sqrt
    · nlinarith [hupper.1, hupper.2]
    · nlinarith [hlower.1, horder]
  have hincreasing := elliptic_increasing_of_mu_positive hmu
  have hnum := hincreasing hcomp_upper hcomp_lower hcomp_order
  have hden := hincreasing hlower hupper horder
  unfold mu
  exact div_lt_div₀ (mul_lt_mul_of_pos_left hnum (by positivity)) hden.le
    (mul_nonneg (by positivity) (ellipticK_nonneg _))
    (ellipticK_positive_of_mu_positive lower (hmu lower hlower))

end SmaleRate.Proofs
