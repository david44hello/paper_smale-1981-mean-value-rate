/-
SmaleRate — exact quartic constant through actual derivative roots.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
import SmaleRate.Proofs.QuarticSelection
import SmaleRate.Proofs.SmallDegreesConcrete
set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SmaleRate.Proofs
open Polynomial Set

theorem quartic_derivative_roots (poly : ℂ[X]) (hpoly : IsPd 4 poly) :
    ∃ first second third : ℂ,
      first ∈ criticalPoints poly ∧ second ∈ criticalPoints poly ∧ third ∈ criticalPoints poly ∧
      poly.derivative = C poly.derivative.leadingCoeff *
        (X - C first) * (X - C second) * (X - C third) := by
  have hderiv_ne : poly.derivative ≠ 0 := by
    intro heq
    exact hpoly.2.2 (by simp [heq])
  have hdegree : poly.derivative.natDegree = 3 := by
    rw [natDegree_derivative, hpoly.1]
  have hsplits := IsAlgClosed.splits poly.derivative
  have hcard : poly.derivative.roots.card = 3 := hsplits.natDegree_eq_card_roots.symm.trans hdegree
  obtain ⟨first, second, third, hroots⟩ := Multiset.card_eq_three.mp hcard
  have hmember (point : ℂ) (hpoint : point ∈ ({first, second, third} : Multiset ℂ)) :
      point ∈ criticalPoints poly := by
    apply (mem_roots hderiv_ne).mp
    rw [hroots]
    exact hpoint
  refine ⟨first, second, third, hmember first (by simp), hmember second (by simp),
    hmember third (by simp), ?_⟩
  simpa [hroots, mul_assoc] using hsplits.eq_prod_roots

theorem quartic_ratio_of_factorization (poly : ℂ[X]) (hpoly : IsPd 4 poly)
    (first second third : ℂ) (hfirst : first ≠ 0) (hsecond : second ≠ 0) (hthird : third ≠ 0)
    (hfactor : poly.derivative = C poly.derivative.leadingCoeff *
      (X - C first) * (X - C second) * (X - C third)) :
    poly.eval first / (first * poly.derivative.eval 0) = quarticRootRatio first second third := by
  let leading := poly.derivative.leadingCoeff
  have hderiv_ne : poly.derivative ≠ 0 := by
    intro heq
    exact hpoly.2.2 (by simp [heq])
  have hleading : leading ≠ 0 := leadingCoeff_ne_zero.mpr hderiv_ne
  have hexpanded : poly.derivative = C leading * X ^ 3 -
      C (leading * (first + second + third)) * X ^ 2 +
      C (leading * (first * second + first * third + second * third)) * X -
      C (leading * first * second * third) := by
    rw [hfactor]
    dsimp only [leading]
    simp only [map_mul, map_add]
    ring
  have hcoeff_zero : poly.coeff 0 = 0 := (coeff_zero_eq_eval_zero poly).trans hpoly.2.1
  have hcoeff_one : poly.coeff 1 = -(leading * first * second * third) := by
    have heq := congrArg (fun polynomial : ℂ[X] => polynomial.coeff 0) hexpanded
    simpa [coeff_derivative] using heq
  have hcoeff_two : poly.coeff 2 =
      leading * (first * second + first * third + second * third) / 2 := by
    have heq := congrArg (fun polynomial : ℂ[X] => polynomial.coeff 1) hexpanded
    norm_num [coeff_derivative, coeff_mul_X_pow', coeff_add] at heq
    apply (eq_div_iff (by norm_num : (2 : ℂ) ≠ 0)).mpr
    linear_combination heq
  have hcoeff_three : poly.coeff 3 = -(leading * (first + second + third)) / 3 := by
    have heq := congrArg (fun polynomial : ℂ[X] => polynomial.coeff 2) hexpanded
    norm_num [coeff_derivative, coeff_mul_X_pow', coeff_add] at heq
    apply (eq_div_iff (by norm_num : (3 : ℂ) ≠ 0)).mpr
    linear_combination heq
  have hcoeff_four : poly.coeff 4 = leading / 4 := by
    have heq := congrArg (fun polynomial : ℂ[X] => polynomial.coeff 3) hexpanded
    norm_num [coeff_derivative, coeff_mul_X_pow', coeff_add] at heq
    apply (eq_div_iff (by norm_num : (4 : ℂ) ≠ 0)).mpr
    linear_combination heq
  have hform : poly.eval first = poly.coeff 4 * first ^ 4 + poly.coeff 3 * first ^ 3 +
      poly.coeff 2 * first ^ 2 + poly.coeff 1 * first := by
    rw [poly.eval_eq_sum_range' (n := 5) (by rw [hpoly.1]; norm_num) first]
    simp [Finset.sum_range_succ, hcoeff_zero]
    <;> ring
  have hderiv_zero : poly.derivative.eval 0 = -(leading * first * second * third) := by
    rw [hfactor]
    simp only [eval_mul, eval_C, eval_sub, eval_X, zero_sub]
    dsimp only [leading]
    ring
  rw [hform, hderiv_zero, hcoeff_one, hcoeff_two, hcoeff_three, hcoeff_four]
  unfold quarticRootRatio
  field_simp [hleading, hfirst, hsecond, hthird]
  <;> ring

theorem quartic_shifted_critical_exists (poly : ℂ[X]) (hpoly : IsPd 4 poly) :
    ∃ point ∈ criticalPoints poly,
      ‖poly.eval point / (point * poly.derivative.eval 0) - 1 / 2‖ ≤ (1 / 4 : ℝ) := by
  obtain ⟨first, second, third, hfirst, hsecond, hthird, hfactor⟩ := quartic_derivative_roots poly hpoly
  have hfirst_ne := critical_nonzero_proved 4 poly hpoly first hfirst
  have hsecond_ne := critical_nonzero_proved 4 poly hpoly second hsecond
  have hthird_ne := critical_nonzero_proved 4 poly hpoly third hthird
  have hratio_first := quartic_ratio_of_factorization poly hpoly first second third
    hfirst_ne hsecond_ne hthird_ne hfactor
  have hfactor_second : poly.derivative = C poly.derivative.leadingCoeff *
      (X - C second) * (X - C first) * (X - C third) := by
    calc
      poly.derivative = C poly.derivative.leadingCoeff *
        (X - C first) * (X - C second) * (X - C third) := hfactor
      _ = _ := by ring
  have hratio_second := quartic_ratio_of_factorization poly hpoly second first third
    hsecond_ne hfirst_ne hthird_ne hfactor_second
  have hfactor_third : poly.derivative = C poly.derivative.leadingCoeff *
      (X - C third) * (X - C first) * (X - C second) := by
    calc
      poly.derivative = C poly.derivative.leadingCoeff *
        (X - C first) * (X - C second) * (X - C third) := hfactor
      _ = _ := by ring
  have hratio_third := quartic_ratio_of_factorization poly hpoly third first second
    hthird_ne hfirst_ne hsecond_ne hfactor_third
  rcases quartic_shifted_selection first second third hfirst_ne hsecond_ne hthird_ne with
    hbound | hbound | hbound
  · exact ⟨first, hfirst, hratio_first.symm ▸ hbound⟩
  · exact ⟨second, hsecond, hratio_second.symm ▸ hbound⟩
  · exact ⟨third, hthird, hratio_third.symm ▸ hbound⟩

theorem quartic_S_upper (poly : ℂ[X]) (hpoly : IsPd 4 poly) : S poly ≤ 3 / 4 := by
  obtain ⟨point, hpoint, hshifted⟩ := quartic_shifted_critical_exists poly hpoly
  exact (s_le_ratio_proved 4 (by omega) poly hpoly point hpoint).trans
    (quartic_ratio_bound_of_shifted _ hshifted)

theorem kd_four_upper : Kd 4 ≤ ((3 / 4 : ℝ) : EReal) := by
  apply iSup_le
  intro poly
  exact_mod_cast quartic_S_upper poly.val poly.property

theorem kd_four_eq : Kd 4 = ((3 / 4 : ℝ) : EReal) := by
  apply le_antisymm kd_four_upper
  have hbound := kd_binomial_lower 4 (by omega)
  norm_num at hbound ⊢
  exact hbound

theorem small_degrees_proved (degree : ℕ) (hlower : 2 ≤ degree) (hupper : degree ≤ 4) :
    Kd degree = ((((degree : ℝ) - 1) / degree : ℝ) : EReal) := by
  by_cases hthree : degree ≤ 3
  · exact small_degrees_two_three degree hlower hthree
  · have hfour : degree = 4 := by omega
    subst degree
    convert kd_four_eq using 1 <;> norm_num

end SmaleRate.Proofs

#check SmaleRate.Proofs.quartic_derivative_roots
#check SmaleRate.Proofs.quartic_ratio_of_factorization
#check SmaleRate.Proofs.quartic_shifted_critical_exists
#check SmaleRate.Proofs.quartic_S_upper
#check SmaleRate.Proofs.kd_four_eq
#check SmaleRate.Proofs.small_degrees_proved
#print axioms SmaleRate.Proofs.quartic_derivative_roots
#print axioms SmaleRate.Proofs.quartic_ratio_of_factorization
#print axioms SmaleRate.Proofs.quartic_shifted_critical_exists
#print axioms SmaleRate.Proofs.quartic_S_upper
#print axioms SmaleRate.Proofs.kd_four_eq
#print axioms SmaleRate.Proofs.small_degrees_proved
