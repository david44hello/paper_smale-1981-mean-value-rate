/-
SmaleRate — quadratic and cubic minimum-ratio upper bounds.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
import SmaleRate.Proofs.PolynomialBasics
set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SmaleRate.Proofs
open Polynomial Set

theorem quadratic_critical_ratio (poly : ℂ[X]) (hpoly : IsPd 2 poly)
    (point : ℂ) (hpoint : point ∈ criticalPoints poly) :
    criticalRatio poly point = 1 / 2 := by
  have hconstant : poly.coeff 0 = 0 := (coeff_zero_eq_eval_zero poly).trans hpoly.2.1
  have hform (member : ℂ) : poly.eval member = poly.coeff 2 * member ^ 2 + poly.coeff 1 * member := by
    rw [poly.eval_eq_sum_range' (n := 3) (by rw [hpoly.1]; norm_num) member]
    simp [Finset.sum_range_succ, hconstant]
    <;> ring
  have hderiv (member : ℂ) : poly.derivative.eval member = 2 * poly.coeff 2 * member + poly.coeff 1 := by
    rw [poly.derivative.eval_eq_sum_range' (n := 2) (by rw [natDegree_derivative, hpoly.1]; norm_num) member]
    simp [Finset.sum_range_succ, coeff_derivative]
    <;> ring
  have hroot : 2 * poly.coeff 2 * point + poly.coeff 1 = 0 := by
    rw [← hderiv]
    exact hpoint
  have hidentity : 2 * poly.eval point = point * poly.derivative.eval 0 := by
    rw [hform, hderiv]
    linear_combination point * hroot
  have hden : point * poly.derivative.eval 0 ≠ 0 :=
    mul_ne_zero (critical_nonzero_proved 2 poly hpoly point hpoint) hpoly.2.2
  have hquotient : poly.eval point / (point * poly.derivative.eval 0) = (1 / 2 : ℂ) := by
    apply (div_eq_iff hden).mpr
    linear_combination (1 / 2 : ℂ) * hidentity
  simp [criticalRatio, hquotient]

theorem quadratic_S (poly : ℂ[X]) (hpoly : IsPd 2 poly) : S poly = 1 / 2 := by
  obtain ⟨_, _, point, hpoint, heq⟩ := minimum_attained_proved 2 (by omega) poly hpoly
  rw [heq, quadratic_critical_ratio poly hpoly point hpoint]

theorem kd_two_upper : Kd 2 ≤ (1 / 2 : ℝ) := by
  apply iSup_le
  intro poly
  exact_mod_cast (quadratic_S poly.val poly.property).le

/-- Coefficient representation, including the derivative, for an arbitrary cubic in the paper class. -/
theorem cubic_eval_forms (poly : ℂ[X]) (hpoly : IsPd 3 poly) :
    (∀ member : ℂ, poly.eval member = poly.coeff 3 * member ^ 3 +
      poly.coeff 2 * member ^ 2 + poly.coeff 1 * member) ∧
    (∀ member : ℂ, poly.derivative.eval member = 3 * poly.coeff 3 * member ^ 2 +
      2 * poly.coeff 2 * member + poly.coeff 1) := by
  have hconstant : poly.coeff 0 = 0 := (coeff_zero_eq_eval_zero poly).trans hpoly.2.1
  constructor
  · intro member
    rw [poly.eval_eq_sum_range' (n := 4) (by rw [hpoly.1]; norm_num) member]
    simp [Finset.sum_range_succ, hconstant]
    <;> ring
  · intro member
    rw [poly.derivative.eval_eq_sum_range' (n := 3) (by rw [natDegree_derivative, hpoly.1]; norm_num) member]
    simp [Finset.sum_range_succ, coeff_derivative]
    <;> ring

/-- Two derivative roots with Vieta's identities; equality of the roots is allowed. -/
theorem cubic_derivative_pair (poly : ℂ[X]) (hpoly : IsPd 3 poly) :
    ∃ first second : ℂ, first ∈ criticalPoints poly ∧ second ∈ criticalPoints poly ∧
      first ≠ 0 ∧ second ≠ 0 ∧
      poly.coeff 1 = 3 * poly.coeff 3 * first * second ∧
      2 * poly.coeff 2 = -(3 * poly.coeff 3 * (first + second)) := by
  obtain ⟨hform, hderiv⟩ := cubic_eval_forms poly hpoly
  obtain ⟨first, hfirst⟩ := critical_points_nonempty 3 (by omega) poly hpoly
  have hpoly_ne : poly ≠ 0 := by
    intro heq
    have hbad := hpoly.2.2
    simp [heq] at hbad
  have hleading : poly.coeff 3 ≠ 0 := by
    rw [← hpoly.1, coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr hpoly_ne
  let second : ℂ := -(2 * poly.coeff 2) / (3 * poly.coeff 3) - first
  have hsum : 2 * poly.coeff 2 = -(3 * poly.coeff 3 * (first + second)) := by
    dsimp [second]
    field_simp [hleading]
    <;> ring
  have hroot : 3 * poly.coeff 3 * first ^ 2 + 2 * poly.coeff 2 * first + poly.coeff 1 = 0 := by
    rw [← hderiv]
    exact hfirst
  have hproduct : poly.coeff 1 = 3 * poly.coeff 3 * first * second := by
    linear_combination hroot - first * hsum
  have hsecond : second ∈ criticalPoints poly := by
    change poly.derivative.eval second = 0
    rw [hderiv, hsum, hproduct]
    ring
  exact ⟨first, second, hfirst, hsecond,
    critical_nonzero_proved 3 poly hpoly first hfirst,
    critical_nonzero_proved 3 poly hpoly second hsecond, hproduct, hsum⟩

theorem cubic_ratio_upper_of_pair (poly : ℂ[X]) (hpoly : IsPd 3 poly)
    (first second : ℂ) (hfirst : first ∈ criticalPoints poly)
    (hfirst_ne : first ≠ 0) (hsecond_ne : second ≠ 0)
    (hproduct : poly.coeff 1 = 3 * poly.coeff 3 * first * second)
    (hsum : 2 * poly.coeff 2 = -(3 * poly.coeff 3 * (first + second)))
    (hnorm : ‖first‖ ≤ ‖second‖) : criticalRatio poly first ≤ 2 / 3 := by
  obtain ⟨hform, hderiv⟩ := cubic_eval_forms poly hpoly
  have hden : first * poly.derivative.eval 0 ≠ 0 := mul_ne_zero hfirst_ne hpoly.2.2
  have hidentity : 6 * second * poly.eval first =
      (3 * second - first) * (first * poly.coeff 1) := by
    rw [hform]
    linear_combination (3 * second * first ^ 2) * hsum +
      (3 * first * second + first ^ 2) * hproduct
  have hquotient : poly.eval first / (first * poly.derivative.eval 0) =
      (1 / 2 : ℂ) - first / (6 * second) := by
    apply (div_eq_iff hden).mpr
    rw [hderiv]
    simp only [zero_pow (by omega : 2 ≠ 0), mul_zero, add_zero, zero_add]
    field_simp [hsecond_ne]
    linear_combination 2 * hidentity
  have hratio : ‖first / (6 * second)‖ ≤ (1 / 6 : ℝ) := by
    rw [norm_div, norm_mul]
    norm_num
    apply (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 6)
      (norm_pos_iff.mpr hsecond_ne))).mpr
    nlinarith
  rw [criticalRatio, hquotient]
  calc
    ‖(1 / 2 : ℂ) - first / (6 * second)‖ ≤ ‖(1 / 2 : ℂ)‖ + ‖first / (6 * second)‖ := norm_sub_le _ _
    _ ≤ 2 / 3 := by norm_num at *; linarith

theorem cubic_S_upper (poly : ℂ[X]) (hpoly : IsPd 3 poly) : S poly ≤ 2 / 3 := by
  obtain ⟨first, second, hfirst, hsecond, hfirst_ne, hsecond_ne, hproduct, hsum⟩ :=
    cubic_derivative_pair poly hpoly
  rcases le_total ‖first‖ ‖second‖ with hnorm | hnorm
  · exact (s_le_ratio_proved 3 (by omega) poly hpoly first hfirst).trans
      (cubic_ratio_upper_of_pair poly hpoly first second hfirst hfirst_ne hsecond_ne hproduct hsum hnorm)
  · have hproduct' : poly.coeff 1 = 3 * poly.coeff 3 * second * first := by
      rw [hproduct]
      ring
    have hsum' : 2 * poly.coeff 2 = -(3 * poly.coeff 3 * (second + first)) := by
      simpa only [add_comm] using hsum
    exact (s_le_ratio_proved 3 (by omega) poly hpoly second hsecond).trans
      (cubic_ratio_upper_of_pair poly hpoly second first hsecond hsecond_ne hfirst_ne hproduct' hsum' hnorm)

theorem kd_three_upper : Kd 3 ≤ (2 / 3 : ℝ) := by
  apply iSup_le
  intro poly
  exact_mod_cast cubic_S_upper poly.val poly.property

end SmaleRate.Proofs

#check SmaleRate.Proofs.quadratic_critical_ratio
#check SmaleRate.Proofs.quadratic_S
#check SmaleRate.Proofs.kd_two_upper
#check SmaleRate.Proofs.cubic_derivative_pair
#check SmaleRate.Proofs.cubic_S_upper
#check SmaleRate.Proofs.kd_three_upper
#print axioms SmaleRate.Proofs.quadratic_S
#print axioms SmaleRate.Proofs.kd_two_upper
#print axioms SmaleRate.Proofs.cubic_derivative_pair
#print axioms SmaleRate.Proofs.cubic_S_upper
#print axioms SmaleRate.Proofs.kd_three_upper
