/-
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
module

public import SmaleRate.Proofs.CapacityUpper
public import SmaleRate.Proofs.BackgroundDeductions
public import SmaleRate.Proofs.XiFull
public import SmaleRate.Proofs.PolynomialBasics
public import SmaleRate.Proofs.InverseBranch
public import SmaleRate.Proofs.ScalarBasics
public import SmaleRate.Proofs.MuLimits
public import SmaleRate.Proofs.DiameterMonotonicity

set_option backward.proofsInPublic true

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set Polynomial

section SourceInputs
variable (hjordan : Background.JordanCurveFact) (hcoefficient : Background.CoefficientUpperFact)
variable (hmu : AntitoneOn mu (Ioo 0 1))
variable (hbets : ∀ (func : ℂ → ℂ), DifferentiableOn ℂ func (disk 1) →
  Bornology.IsBounded (func '' disk 1) → func 0 = 0 →
  (∃ first ∈ disk 1, ∃ second ∈ disk 1, func first ≠ func second) →
  ∀ point ∈ disk 1, point ≠ 0 →
    ‖func point‖ ≤ 4 * transfiniteDiameter (func '' disk 1) * Real.exp (-mu ‖point‖))
include hjordan hcoefficient hmu hbets

theorem normalized_polynomial_bound_given_facts (degree : ℕ) (hdegree : 2 ≤ degree)
    (poly : ℂ[X]) (hpoly : IsPd degree poly) (critical : ℂ)
    (hnormal : NormalizedCriticalValues poly critical) (hpositive : 0 < S poly)
    (height : ℝ) (hheight : height ∈ Ioo 0 1) : S poly ≤ yBound degree height := by
  obtain ⟨inverse, hinverse⟩ := inverse_branch_exists_proved degree hdegree poly hpoly critical hnormal
  have hproperties := inverse_branch_properties_of_ratio degree poly hpoly critical hnormal inverse hinverse
    (s_le_ratio_proved degree hdegree poly hpoly critical hnormal.1)
  have hcritical := normalized_critical_ne_zero degree poly hpoly critical hnormal
  obtain ⟨hgeometry, hbase, hminusone⟩ := exterior_image_geometry_given_jordan hjordan
    inverse hproperties.1 hinverse.2.1 height hheight critical hcritical hproperties.2.2.1
  obtain ⟨func, hfunc, hzero⟩ := riemann_map_given_jordan hjordan
    (exteriorImage inverse height critical) hgeometry hbase
  rw [← hfunc.2] at hminusone
  obtain ⟨xi, hxi, hminusone⟩ := hminusone
  have hxi_bound := xi_bound_proved degree hdegree poly hpoly critical hnormal inverse hinverse
    height hheight func hfunc hzero xi hxi hminusone
  have hnonconstant : ∃ first ∈ disk 1, ∃ second ∈ disk 1, func first ≠ func second := by
    refine ⟨0, by simp [disk], xi, hxi, ?_⟩
    rw [hzero, hminusone]
    norm_num
  have hbounded : Bornology.IsBounded (func '' disk 1) := by
    rw [hfunc.2]
    exact hgeometry.2.2.2.1
  have hestimate := hbets func hfunc.1.1 hbounded hzero hnonconstant xi hxi hxi_bound.1
  have hestimate' : 1 ≤ 4 * transfiniteDiameter (exteriorImage inverse height critical) * Real.exp (-mu ‖xi‖) := by
    simpa only [hminusone, norm_neg, norm_one, hfunc.2] using hestimate
  have hderivative : 0 < ‖deriv inverse 0‖ :=
    norm_pos_iff.mpr (univalent_deriv_ne_zero inverse hproperties.1 0 (by simp [disk]))
  have hcriticalnorm : 0 < ‖critical‖ := norm_pos_iff.mpr hcritical
  have hcap := capacity_exterior_upper_given_facts hjordan hcoefficient inverse hproperties.1
    hinverse.2.1 height hheight critical hcritical hproperties.2.2.1
  have hcap_scalar := hcap.trans (capacity_step_scalar (S poly) height ‖deriv inverse 0‖ ‖critical‖
    (‖critical‖ / (height * ‖deriv inverse 0‖)) hpositive hheight.1 hderivative hcriticalnorm
    hproperties.2.2.2 rfl)
  have hdiam := transfiniteDiameter_mono_of_compact (exteriorImage inverse height critical)
    (closure (exteriorImage inverse height critical)) ⟨0, hbase⟩ subset_closure
    hgeometry.2.2.2.1.isCompact_closure
  have hcap_final : transfiniteDiameter (exteriorImage inverse height critical) ≤ 1 / (height * S poly) :=
    hdiam.trans hcap_scalar
  have hdegreepos : 0 < (degree : ℝ) := by exact_mod_cast (show 0 < degree by omega)
  have houter : height ^ (1 / (degree : ℝ)) ∈ Ioo 0 1 :=
    ⟨Real.rpow_pos_of_pos hheight.1 _, Real.rpow_lt_one hheight.1.le hheight.2 (one_div_pos.mpr hdegreepos)⟩
  have hinner : ‖xi‖ ∈ Ioo 0 1 := ⟨norm_pos_iff.mpr hxi_bound.1, mem_ball_zero_iff.mp hxi⟩
  exact final_scalar_deduction (S poly) height ‖xi‖ (height ^ (1 / (degree : ℝ)))
    (transfiniteDiameter (exteriorImage inverse height critical)) hpositive hheight.1
    hinner houter hxi_bound.2 hmu hcap_final hestimate'

theorem polynomial_bound_given_facts (degree : ℕ) (hdegree : 2 ≤ degree)
    (poly : ℂ[X]) (hpoly : IsPd degree poly) (height : ℝ) (hheight : height ∈ Ioo 0 1) :
    S poly ≤ yBound degree height := by
  by_cases hpositive : 0 < S poly
  · have hvalues : ∀ point ∈ criticalPoints poly, poly.eval point ≠ 0 := by
      intro point hpoint hzero
      have hs := zero_critical_value_proved degree hdegree poly hpoly point hpoint hzero
      linarith
    obtain ⟨scalar, hscalar, critical, hnormal⟩ :=
      critical_value_normalization_proved degree hdegree poly hpoly hvalues
    have hscalar_ne : (scalar : ℂ) ≠ 0 := by exact_mod_cast hscalar.ne'
    have hscale := scalar_invariance_proved degree hdegree poly hpoly (scalar : ℂ) hscalar_ne
    have hnormalized := normalized_polynomial_bound_given_facts hjordan hcoefficient hmu hbets
      degree hdegree (Polynomial.C (scalar : ℂ) * poly) hscale.1 critical hnormal
      (by simpa only [hscale.2.2] using hpositive) height hheight
    simpa only [hscale.2.2] using hnormalized
  · apply (le_of_not_gt hpositive).trans
    unfold yBound
    have hheightpos := hheight.1
    positivity

end SourceInputs
end SmaleRate.Proofs
