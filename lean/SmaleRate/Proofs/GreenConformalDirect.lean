/-
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
module

public import SmaleRate.Proofs.GreenPullback

set_option backward.proofsInPublic true

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set Filter Metric InnerProductSpace
open scoped Topology

def conformalGreenPullback (equiv : OpenPartialHomeomorph ℂ ℂ) (green : ℂ → ℝ)
    (point : ℂ) : ℝ := by
  classical
  exact if point ∈ equiv.source then green (equiv point) else 0

theorem finite_green_pullback (equiv : OpenPartialHomeomorph ℂ ℂ)
    (hbounded : Bornology.IsBounded equiv.source) (pole : ℂ) (hpole : pole ∈ equiv.source)
    (hanalytic : AnalyticOnNhd ℂ (equiv : ℂ → ℂ) equiv.source)
    (hderivative : deriv (equiv : ℂ → ℂ) pole ≠ 0)
    (green : ℂ → ℝ) (hgreen : IsClassicalGreen equiv.target (equiv pole) green) :
    IsClassicalGreen equiv.source pole (conformalGreenPullback equiv green) := by
  classical
  obtain ⟨regular, hregular, heqregular⟩ := hgreen.2.2.2.2.1
  have hne (point : ℂ) (hpoint : point ∈ equiv.source) (hdistinct : point ≠ pole) :
      equiv point ≠ equiv pole := fun heq => hdistinct (equiv.injOn hpoint hpole heq)
  refine ⟨hbounded, hpole, ?_, ?_, ?_, ?_, ?_⟩
  · intro point hpoint
    have hdistinct : point ≠ pole := by simpa using hpoint.2
    have hcomp := harmonic_comp_analytic green (equiv : ℂ → ℂ) point
      (hgreen.2.2.1 _ ⟨equiv.map_source hpoint.1, by simpa using hne point hpoint.1 hdistinct⟩)
      (hanalytic point hpoint.1)
    apply (harmonicAt_congr_nhds (f₁ := conformalGreenPullback equiv green)
      (f₂ := green ∘ (equiv : ℂ → ℂ)) ?_).mpr hcomp
    filter_upwards [equiv.open_source.mem_nhds hpoint.1] with member hmember
    simp only [conformalGreenPullback, if_pos hmember, Function.comp_apply]
  · intro point hpoint
    have hdistinct : point ≠ pole := by simpa using hpoint.2
    simp only [conformalGreenPullback, if_pos hpoint.1]
    exact hgreen.2.2.2.1 _ ⟨equiv.map_source hpoint.1, by simpa using hne point hpoint.1 hdistinct⟩
  · have hslope : AnalyticAt ℂ (dslope (equiv : ℂ → ℂ) pole) pole := by
      obtain ⟨series, hseries⟩ := hanalytic pole hpole
      exact ⟨series.fslope, hseries.has_fpower_series_dslope_fslope⟩
    have hslope_ne : dslope (equiv : ℂ → ℂ) pole pole ≠ 0 := by
      rw [dslope_same]
      exact hderivative
    have hmap : Tendsto (equiv : ℂ → ℂ) (𝓝[≠] pole) (𝓝[≠] (equiv pole)) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨(hanalytic pole hpole).continuousAt.tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
      filter_upwards [nhdsWithin_le_nhds (equiv.open_source.mem_nhds hpole),
        self_mem_nhdsWithin] with member hmember hmember_ne
      exact hne member hmember (by simpa using hmember_ne)
    refine ⟨fun member => regular (equiv member) -
      Real.log ‖dslope (equiv : ℂ → ℂ) pole member‖, ?_, ?_⟩
    · exact (harmonic_comp_analytic regular (equiv : ℂ → ℂ) pole hregular
        (hanalytic pole hpole)).sub (hslope.harmonicAt_log_norm hslope_ne)
    · filter_upwards [hmap.eventually heqregular,
        nhdsWithin_le_nhds (equiv.open_source.mem_nhds hpole), self_mem_nhdsWithin]
        with member hregular_member hmember hmember_ne
      have hdistinct : member ≠ pole := by simpa using hmember_ne
      have hquotient : dslope (equiv : ℂ → ℂ) pole member =
          (equiv member - equiv pole) / (member - pole) := by
        rw [dslope_of_ne _ hdistinct, slope_def_field]
      have hlog : Real.log ‖dslope (equiv : ℂ → ℂ) pole member‖ =
          Real.log ‖equiv member - equiv pole‖ - Real.log ‖member - pole‖ := by
        rw [hquotient, norm_div, Real.log_div
          (norm_ne_zero_iff.mpr (sub_ne_zero.mpr (hne member hmember hdistinct)))
          (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hdistinct))]
      simp only [conformalGreenPullback, if_pos hmember]
      linarith
  · intro point hpoint
    apply (finite_green_boundary_comp equiv pole hpole green hgreen point hpoint).congr'
    filter_upwards [self_mem_nhdsWithin] with member hmember
    simp only [conformalGreenPullback, if_pos hmember, Function.comp_apply]
  · intro point hpoint
    simp only [conformalGreenPullback, if_neg hpoint]

theorem finite_green_conformal_proved
    (domain image : Set ℂ) (hdomain : IsBoundedJordanDomain domain)
    (himage : IsBoundedJordanDomain image) (func : ℂ → ℂ)
    (hfunc : IsConformalOnto func domain image) (pole point : ℂ)
    (hpole : pole ∈ domain) (hpoint : point ∈ domain) (hdistinct : point ≠ pole)
    (greenDomain greenImage : ℂ → ℝ)
    (hgreenDomain : IsClassicalGreen domain pole greenDomain)
    (hgreenImage : IsClassicalGreen image (func pole) greenImage) :
    greenImage (func point) = greenDomain point := by
  classical
  let equiv : OpenPartialHomeomorph ℂ ℂ := univalentOpenPartialHomeomorph func domain
    hdomain.1 hdomain.2.1 hdomain.2.2.1 hfunc.1
  have htarget : equiv.target = image := hfunc.2
  have hanalytic : AnalyticOnNhd ℂ (equiv : ℂ → ℂ) equiv.source :=
    (Complex.analyticOnNhd_iff_differentiableOn hdomain.1).mpr hfunc.1.1
  have hderivative : deriv (equiv : ℂ → ℂ) pole ≠ 0 :=
    univalent_domain_deriv_ne_zero func domain hdomain.1 hdomain.2.1 hdomain.2.2.1
      hfunc.1 pole hpole
  have hpullback := finite_green_pullback equiv hdomain.2.2.2.1 pole hpole hanalytic
    hderivative greenImage (by rw [htarget]; exact hgreenImage)
  have heq := finite_green_unique domain hdomain.1 hdomain.2.1 pole
    (conformalGreenPullback equiv greenImage) greenDomain hpullback hgreenDomain point hdistinct
  have hsource_point : point ∈ equiv.source := hpoint
  change (if point ∈ equiv.source then greenImage (equiv point) else 0) = greenDomain point at heq
  rw [if_pos hsource_point] at heq
  exact heq

end SmaleRate.Proofs

#check SmaleRate.Proofs.finite_green_pullback
#print axioms SmaleRate.Proofs.finite_green_pullback
#check SmaleRate.Proofs.finite_green_conformal_proved
#print axioms SmaleRate.Proofs.finite_green_conformal_proved
