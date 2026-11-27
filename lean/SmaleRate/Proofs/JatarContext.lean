/-
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
module

public import SmaleRate.Proofs.JnBoundary
public import SmaleRate.Proofs.PolynomialBasics

set_option backward.proofsInPublic true

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set Polynomial

theorem jatar_printed_bound_from_sources
    (hsource : ∀ degree : ℕ, 169 ≤ degree → ∀ poly : ℂ[X], IsSchlichtNormalized degree poly →
      (Real.log (1/‖poly.leadingCoeff‖))^2 ≤ (degree : ℝ) → ∀ point : ℂ,
      point ∈ criticalPoints poly → point ∈ frontier (lemniscateComponent poly 1) →
      criticalRatio poly point ≤ jatarNgBound degree)
    (hleadingSource : ∀ degree : ℕ, 2 ≤ degree → ∀ poly : ℂ[X],
      IsSchlichtNormalized degree poly → ‖poly.leadingCoeff‖ < 1)
    (degree : ℕ) (hdegree : 169 ≤ degree) (poly : ℂ[X])
    (hpoly : IsSchlichtNormalized degree poly)
    (hleading : Real.exp (-Real.sqrt degree) ≤ ‖poly.leadingCoeff‖) :
    S poly ≤ jatarNgBound degree := by
  have hdegree_two : 2 ≤ degree := by omega
  have hpositive : 0 < ‖poly.leadingCoeff‖ := (Real.exp_pos _).trans_le hleading
  have hless : ‖poly.leadingCoeff‖ < 1 := hleadingSource degree hdegree_two poly hpoly
  have hlog_lower : -Real.sqrt degree ≤ Real.log ‖poly.leadingCoeff‖ :=
    (Real.le_log_iff_exp_le hpositive).mpr hleading
  have hlog_negative : Real.log ‖poly.leadingCoeff‖ < 0 := Real.log_neg hpositive hless
  have hlog : (Real.log (1/‖poly.leadingCoeff‖))^2 ≤ (degree : ℝ) := by
    rw [one_div, Real.log_inv]
    have hsqrt : 0 ≤ Real.sqrt (degree : ℝ) := Real.sqrt_nonneg _
    have hsquare : (Real.sqrt (degree : ℝ))^2 = (degree : ℝ) := Real.sq_sqrt (by positivity)
    nlinarith
  obtain ⟨point, hboundary, hcritical⟩ :=
    jatar_ng_boundary_critical_exists_proved degree hdegree_two poly hpoly
  exact (s_le_ratio_proved degree hdegree_two poly hpoly.1 point hcritical).trans
    (hsource degree hdegree poly hpoly hlog point hcritical hboundary)

end SmaleRate.Proofs
