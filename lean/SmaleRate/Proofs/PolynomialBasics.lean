/-
SmaleRate — polynomial minimum and normalization leaves.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
-- Integrated by : proof declarations unchanged; trailing diagnostic commands removed.
module

public import SmaleRate.Defs.Basic

set_option backward.proofsInPublic true

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SmaleRate.Proofs
open Polynomial Set

theorem critical_nonzero_proved (degree : ℕ) (poly : ℂ[X]) (hpoly : IsPd degree poly) :
    ∀ point ∈ criticalPoints poly, point ≠ 0 := by
  intro point hpoint hzero
  subst point
  exact hpoly.2.2 hpoint

theorem critical_ratio_norm_formula_proved (poly : ℂ[X]) (point : ℂ) :
    criticalRatio poly point = ‖poly.eval point‖ / (‖point‖ * ‖poly.derivative.eval 0‖) := by
  simp [criticalRatio]

theorem critical_points_finite (poly : ℂ[X]) (hderivative : poly.derivative.eval 0 ≠ 0) :
    (criticalPoints poly).Finite := by
  have hne : poly.derivative ≠ 0 := by
    intro hzero
    apply hderivative
    simp [hzero]
  exact Polynomial.finite_setOfPred_isRoot hne

theorem critical_points_nonempty (degree : ℕ) (hdegree : 2 ≤ degree)
    (poly : ℂ[X]) (hpoly : IsPd degree poly) : (criticalPoints poly).Nonempty := by
  have hpos : 0 < poly.derivative.natDegree := by
    rw [Polynomial.natDegree_derivative, hpoly.1]
    omega
  obtain ⟨point, hpoint⟩ := Complex.exists_root (Polynomial.natDegree_pos_iff_degree_pos.mp hpos)
  exact ⟨point, hpoint⟩

theorem critical_ratios_finite (degree : ℕ) (poly : ℂ[X]) (hpoly : IsPd degree poly) :
    (criticalRatios poly).Finite :=
  (critical_points_finite poly hpoly.2.2).image (criticalRatio poly)

theorem critical_ratios_nonempty (degree : ℕ) (hdegree : 2 ≤ degree)
    (poly : ℂ[X]) (hpoly : IsPd degree poly) : (criticalRatios poly).Nonempty :=
  (critical_points_nonempty degree hdegree poly hpoly).image (criticalRatio poly)

theorem minimum_attained_proved (degree : ℕ) (hdegree : 2 ≤ degree) (poly : ℂ[X])
    (hpoly : IsPd degree poly) :
    (criticalPoints poly).Finite ∧ (criticalPoints poly).Nonempty ∧
    ∃ point ∈ criticalPoints poly, S poly = criticalRatio poly point := by
  have hfinite := critical_points_finite poly hpoly.2.2
  have hnonempty := critical_points_nonempty degree hdegree poly hpoly
  have hmem : S poly ∈ criticalRatios poly :=
    (critical_ratios_nonempty degree hdegree poly hpoly).csInf_mem
      (critical_ratios_finite degree poly hpoly)
  obtain ⟨point, hpoint, heq⟩ := hmem
  exact ⟨hfinite, hnonempty, point, hpoint, heq.symm⟩

theorem s_nonneg_proved (degree : ℕ) (hdegree : 2 ≤ degree) (poly : ℂ[X])
    (hpoly : IsPd degree poly) : 0 ≤ S poly := by
  obtain ⟨_, _, point, _, heq⟩ := minimum_attained_proved degree hdegree poly hpoly
  rw [heq]
  exact norm_nonneg _

theorem s_le_ratio_proved (degree : ℕ) (_hdegree : 2 ≤ degree) (poly : ℂ[X])
    (hpoly : IsPd degree poly) (point : ℂ) (hpoint : point ∈ criticalPoints poly) :
    S poly ≤ criticalRatio poly point := by
  apply csInf_le (critical_ratios_finite degree poly hpoly).bddBelow
  exact ⟨point, hpoint, rfl⟩

theorem zero_critical_value_proved (degree : ℕ) (hdegree : 2 ≤ degree) (poly : ℂ[X])
    (hpoly : IsPd degree poly) (point : ℂ) (hpoint : point ∈ criticalPoints poly)
    (hvalue : poly.eval point = 0) : S poly = 0 := by
  apply le_antisymm _ (s_nonneg_proved degree hdegree poly hpoly)
  simpa [criticalRatio, hvalue] using s_le_ratio_proved degree hdegree poly hpoly point hpoint

theorem s_pos_of_critical_values_ne_zero_proved (degree : ℕ) (hdegree : 2 ≤ degree)
    (poly : ℂ[X]) (hpoly : IsPd degree poly)
    (hvalues : ∀ point ∈ criticalPoints poly, poly.eval point ≠ 0) : 0 < S poly := by
  obtain ⟨_, _, point, hpoint, heq⟩ := minimum_attained_proved degree hdegree poly hpoly
  rw [heq, criticalRatio]
  exact norm_pos_iff.mpr (div_ne_zero (hvalues point hpoint)
    (mul_ne_zero (critical_nonzero_proved degree poly hpoly point hpoint) hpoly.2.2))

theorem scaled_critical_points (poly : ℂ[X]) (scalar : ℂ) (hscalar : scalar ≠ 0) :
    criticalPoints (C scalar * poly) = criticalPoints poly := by
  ext point
  simp [criticalPoints, hscalar]

theorem scaled_critical_ratio (poly : ℂ[X]) (scalar : ℂ) (hscalar : scalar ≠ 0) (point : ℂ) :
    criticalRatio (C scalar * poly) point = criticalRatio poly point := by
  unfold criticalRatio
  simp only [derivative_C_mul, eval_C_mul]
  congr 1
  rw [mul_left_comm point scalar (poly.derivative.eval 0), mul_div_mul_left _ _ hscalar]

theorem scaled_critical_ratios (poly : ℂ[X]) (scalar : ℂ) (hscalar : scalar ≠ 0) :
    criticalRatios (C scalar * poly) = criticalRatios poly := by
  rw [criticalRatios, scaled_critical_points poly scalar hscalar]
  congr 1
  funext point
  exact scaled_critical_ratio poly scalar hscalar point

theorem scaled_S (poly : ℂ[X]) (scalar : ℂ) (hscalar : scalar ≠ 0) :
    S (C scalar * poly) = S poly := by
  unfold S
  rw [scaled_critical_ratios poly scalar hscalar]

theorem scaled_isPd (degree : ℕ) (poly : ℂ[X]) (hpoly : IsPd degree poly)
    (scalar : ℂ) (hscalar : scalar ≠ 0) : IsPd degree (C scalar * poly) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [natDegree_C_mul_of_isUnit (isUnit_iff_ne_zero.mpr hscalar), hpoly.1]
  · simp [hpoly.2.1]
  · simpa [derivative_C_mul, eval_C_mul] using mul_ne_zero hscalar hpoly.2.2

theorem scalar_invariance_proved (degree : ℕ) (_hdegree : 2 ≤ degree) (poly : ℂ[X])
    (hpoly : IsPd degree poly) (scalar : ℂ) (hscalar : scalar ≠ 0) :
    IsPd degree (C scalar * poly) ∧ criticalPoints (C scalar * poly) = criticalPoints poly ∧
    S (C scalar * poly) = S poly :=
  ⟨scaled_isPd degree poly hpoly scalar hscalar, scaled_critical_points poly scalar hscalar,
    scaled_S poly scalar hscalar⟩

theorem critical_value_normalization_proved (degree : ℕ) (hdegree : 2 ≤ degree)
    (poly : ℂ[X]) (hpoly : IsPd degree poly)
    (hvalues : ∀ point ∈ criticalPoints poly, poly.eval point ≠ 0) :
    ∃ scalar : ℝ, 0 < scalar ∧ ∃ point : ℂ,
      NormalizedCriticalValues (C (scalar : ℂ) * poly) point := by
  let values : Set ℝ := (fun point : ℂ => ‖poly.eval point‖) '' criticalPoints poly
  have hfinite : values.Finite := (critical_points_finite poly hpoly.2.2).image _
  have hnonempty : values.Nonempty := (critical_points_nonempty degree hdegree poly hpoly).image _
  obtain ⟨point, hpoint, heq⟩ := hnonempty.csInf_mem hfinite
  change ‖poly.eval point‖ = sInf values at heq
  have hpositive : 0 < ‖poly.eval point‖ := norm_pos_iff.mpr (hvalues point hpoint)
  refine ⟨(‖poly.eval point‖)⁻¹, inv_pos.mpr hpositive, point, ?_, ?_, ?_⟩
  · rw [scaled_critical_points poly _ (by exact_mod_cast (inv_ne_zero hpositive.ne'))]
    exact hpoint
  · simp only [eval_C_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hpositive)]
    exact inv_mul_cancel₀ hpositive.ne'
  · intro other hother
    rw [scaled_critical_points poly _ (by exact_mod_cast (inv_ne_zero hpositive.ne'))] at hother
    have hle : ‖poly.eval point‖ ≤ ‖poly.eval other‖ := by
      rw [heq]
      exact csInf_le hfinite.bddBelow ⟨other, hother, rfl⟩
    simp only [eval_C_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hpositive)]
    calc
      1 = (‖poly.eval point‖)⁻¹ * ‖poly.eval point‖ := (inv_mul_cancel₀ hpositive.ne').symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hle (inv_nonneg.mpr hpositive.le)

end SmaleRate.Proofs
