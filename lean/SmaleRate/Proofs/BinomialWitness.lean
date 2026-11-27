/-
SmaleRate — exact binomial lower witness.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
module

public import SmaleRate.Proofs.PolynomialBasics
public import SmaleRate.Proofs.PolynomialWitness

set_option backward.proofsInPublic true

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SmaleRate.Proofs
open Polynomial Set

theorem binomial_isPd (degree : ℕ) (hdegree : 2 ≤ degree) :
    IsPd degree (X ^ degree + X : ℂ[X]) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [natDegree_add_eq_left_of_natDegree_lt]
    · simp
    · simp only [natDegree_X, natDegree_X_pow]
      omega
  · simp [show degree ≠ 0 by omega]
  · simp [derivative_add, derivative_pow, show degree - 1 ≠ 0 by omega]

theorem binomial_critical_ratio (degree : ℕ) (hdegree : 2 ≤ degree)
    (point : ℂ) (hpoint : point ∈ criticalPoints (X ^ degree + X : ℂ[X])) :
    criticalRatio (X ^ degree + X : ℂ[X]) point = ((degree : ℝ) - 1) / degree := by
  have hdegree_ne : (degree : ℂ) ≠ 0 := by exact_mod_cast (show degree ≠ 0 by omega)
  have hpoint_ne := critical_nonzero_proved degree _ (binomial_isPd degree hdegree) point hpoint
  have hderivative : (X ^ degree + X : ℂ[X]).derivative.eval 0 = 1 := by
    simp [derivative_add, derivative_pow, show degree - 1 ≠ 0 by omega]
  have hroot : (degree : ℂ) * point ^ (degree - 1) + 1 = 0 := by
    simpa [criticalPoints, derivative_add, derivative_pow, mul_comm] using hpoint
  have hpower : point ^ degree = point ^ (degree - 1) * point := by
    rw [← pow_succ]
    congr 1
    omega
  have hquotient : (X ^ degree + X : ℂ[X]).eval point /
      (point * (X ^ degree + X : ℂ[X]).derivative.eval 0) =
      ((degree : ℂ) - 1) / degree := by
    simp only [eval_add, eval_pow, eval_X, hderivative, mul_one, hpower]
    field_simp [hpoint_ne, hdegree_ne]
    linear_combination hroot
  rw [criticalRatio, hquotient]
  have hreal : 0 ≤ ((degree : ℝ) - 1) / degree := by
    have hdegree_real : (2 : ℝ) ≤ degree := by exact_mod_cast hdegree
    exact div_nonneg (by linarith) (by positivity)
  simpa only [← Complex.ofReal_natCast, ← Complex.ofReal_one, ← Complex.ofReal_sub,
    ← Complex.ofReal_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hreal]

theorem binomial_critical_ratios (degree : ℕ) (hdegree : 2 ≤ degree) :
    criticalRatios (X ^ degree + X : ℂ[X]) = {((degree : ℝ) - 1) / degree} := by
  ext value
  constructor
  · rintro ⟨point, hpoint, rfl⟩
    exact binomial_critical_ratio degree hdegree point hpoint
  · intro hvalue
    obtain ⟨point, hpoint⟩ := critical_points_nonempty degree hdegree _ (binomial_isPd degree hdegree)
    exact ⟨point, hpoint, (binomial_critical_ratio degree hdegree point hpoint).trans hvalue.symm⟩

theorem binomial_S (degree : ℕ) (hdegree : 2 ≤ degree) :
    S (X ^ degree + X : ℂ[X]) = ((degree : ℝ) - 1) / degree := by
  rw [S, binomial_critical_ratios degree hdegree, csInf_singleton]

theorem kd_binomial_lower (degree : ℕ) (hdegree : 2 ≤ degree) :
    ((((degree : ℝ) - 1) / degree : ℝ) : EReal) ≤ Kd degree := by
  have hbound : (S (X ^ degree + X : ℂ[X]) : EReal) ≤ Kd degree :=
    le_iSup_of_le ⟨_, binomial_isPd degree hdegree⟩ le_rfl
  simpa only [binomial_S degree hdegree] using hbound

end SmaleRate.Proofs

#check SmaleRate.Proofs.binomial_critical_ratio
#check SmaleRate.Proofs.binomial_critical_ratios
#check SmaleRate.Proofs.binomial_S
#check SmaleRate.Proofs.kd_binomial_lower
#print axioms SmaleRate.Proofs.binomial_critical_ratio
#print axioms SmaleRate.Proofs.binomial_critical_ratios
#print axioms SmaleRate.Proofs.binomial_S
#print axioms SmaleRate.Proofs.kd_binomial_lower
