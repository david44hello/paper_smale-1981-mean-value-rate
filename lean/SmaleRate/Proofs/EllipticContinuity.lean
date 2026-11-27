/-
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
import SmaleRate.Proofs.EllipticOrder

noncomputable section
namespace SmaleRate.Proofs
open Set Filter MeasureTheory
open scoped Topology

theorem elliptic_integrand_arg_pos (modulus param : ℝ)
    (hmodulus : modulus ∈ Ioo 0 1) (hparam : param ∈ Ioo 0 1) :
    0 < (1-param^2)*(1-modulus^2*param^2) := by
  have hparam_sq : param^2 < 1 := by nlinarith [hparam.1, hparam.2]
  have hmodulus_sq : modulus^2 < 1 := by nlinarith [hmodulus.1, hmodulus.2]
  apply mul_pos (by linarith)
  nlinarith [mul_pos (by linarith : 0 < 1-modulus^2) (sq_pos_of_pos hparam.1)]

theorem ellipticK_continuousAt_of_positive
    (hmu : ∀ modulus ∈ Ioo 0 1, 0 < mu modulus)
    (modulus : ℝ) (hmodulus : modulus ∈ Ioo 0 1) : ContinuousAt ellipticK modulus := by
  let upper : ℝ := (modulus + 1) / 2
  have hupper : upper ∈ Ioo 0 1 := by dsimp [upper]; constructor <;> linarith [hmodulus.1, hmodulus.2]
  have hgap : modulus < upper := by dsimp [upper]; linarith [hmodulus.2]
  apply intervalIntegral.continuousAt_of_dominated_interval
    (bound := fun param : ℝ => 1 / Real.sqrt ((1-param^2)*(1-upper^2*param^2)))
  · exact Eventually.of_forall (fun radius =>
      (show Measurable (fun param : ℝ =>
        1 / Real.sqrt ((1-param^2)*(1-radius^2*param^2))) by fun_prop).aestronglyMeasurable)
  · filter_upwards [Ioo_mem_nhds hmodulus.1 hgap] with radius hradius
    filter_upwards with param hparam
    have hparam' : param ∈ Ioc (0 : ℝ) 1 := by simpa only [uIoc_of_le zero_le_one] using hparam
    by_cases hendpoint : param = 1
    · subst param
      norm_num
    · have hparam_open : param ∈ Ioo (0 : ℝ) 1 := ⟨hparam'.1, lt_of_le_of_ne hparam'.2 hendpoint⟩
      rw [Real.norm_eq_abs, abs_of_nonneg (one_div_nonneg.mpr (Real.sqrt_nonneg _))]
      exact (elliptic_integrand_strict radius upper param
        ⟨hradius.1, hradius.2.trans hupper.2⟩ hupper hradius.2 hparam_open).le
  · exact elliptic_integrable_of_mu_positive upper (hmu upper hupper)
  · filter_upwards with param hparam
    have hparam' : param ∈ Ioc (0 : ℝ) 1 := by simpa only [uIoc_of_le zero_le_one] using hparam
    by_cases hendpoint : param = 1
    · subst param
      convert (continuousAt_const : ContinuousAt (fun _ : ℝ => (0 : ℝ)) modulus) using 1
      ext radius
      norm_num
    · have hparam_open : param ∈ Ioo (0 : ℝ) 1 := ⟨hparam'.1, lt_of_le_of_ne hparam'.2 hendpoint⟩
      exact continuousAt_const.div (by fun_prop)
        (ne_of_gt (Real.sqrt_pos.mpr (elliptic_integrand_arg_pos modulus param hmodulus hparam_open)))

theorem mu_continuousAt_of_positive
    (hmu : ∀ modulus ∈ Ioo 0 1, 0 < mu modulus)
    (modulus : ℝ) (hmodulus : modulus ∈ Ioo 0 1) : ContinuousAt mu modulus := by
  have hcomp := complement_mem modulus hmodulus
  have hcomp_cont : ContinuousAt complement modulus := by unfold complement; fun_prop
  exact (continuousAt_const.mul
    ((ellipticK_continuousAt_of_positive hmu (complement modulus) hcomp).comp hcomp_cont)).div
    (ellipticK_continuousAt_of_positive hmu modulus hmodulus)
    (ne_of_gt (ellipticK_positive_of_mu_positive modulus (hmu modulus hmodulus)))

end SmaleRate.Proofs
