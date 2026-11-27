/-
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
module

public import SmaleRate.Proofs.GreenUniqueness
public import SmaleRate.Proofs.ExteriorGeometryConcrete

set_option backward.proofsInPublic true

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set Filter Metric InnerProductSpace
open scoped Topology

theorem harmonic_comp_analytic (green : ℂ → ℝ) (func : ℂ → ℂ) (point : ℂ)
    (hgreen : HarmonicAt green (func point)) (hfunc : AnalyticAt ℂ func point) :
    HarmonicAt (green ∘ func) point := by
  obtain ⟨radius, hradius, hball⟩ := Metric.eventually_nhds_iff_ball.mp hgreen.eventually
  obtain ⟨analytic, hanalytic, hreal⟩ :=
    (show HarmonicOnNhd green (ball (func point) radius) from hball).exists_analyticOnNhd_ball_re_eq
  have hbase : func point ∈ ball (func point) radius := mem_ball_self hradius
  have hcomp := ((hanalytic (func point) hbase).comp hfunc).harmonicAt_re
  apply (harmonicAt_congr_nhds (f₁ := green ∘ func)
    (f₂ := fun member : ℂ => (analytic (func member)).re) ?_).mpr hcomp
  filter_upwards [hfunc.continuousAt.preimage_mem_nhds (isOpen_ball.mem_nhds hbase)] with member hmember
  exact (hreal hmember).symm

theorem inversion_analytic (critical point : ℂ) (hpoint : point ≠ 0) :
    AnalyticAt ℂ (inversion critical) point := by
  exact analyticAt_const.div analyticAt_id hpoint

def inversionGreen (critical : ℂ) (green : ℂ → ℝ) (point : ℂ) : ℝ :=
  if point = 0 then 0 else green (inversion critical point)

theorem invertedExterior_green (domain : Set ℂ) (hopen : IsOpen domain)
    (hbounded : Bornology.IsBounded domain) (hzero : (0 : ℂ) ∈ domain)
    (hregular : interior (closure domain) = domain)
    (critical : ℂ) (hcritical : critical ≠ 0) (green : ℂ → ℝ)
    (hgreen : IsClassicalExteriorGreen (closure domain) green) :
    IsClassicalGreen (invertedExterior domain critical) 0 (inversionGreen critical green) := by
  classical
  obtain ⟨hharmonic, hpositive, ⟨regular, hregular_harmonic, hregular_eq⟩,
    hboundary, houtside⟩ := hgreen
  have hcriticalnorm : ‖critical‖ ≠ 0 := norm_ne_zero_iff.mpr hcritical
  have hfrontier : frontier (closure domain) = frontier domain := by
    simp only [frontier, closure_closure, hregular, hopen.interior_eq]
  refine ⟨invertedExterior_bounded domain hopen hzero critical hcritical,
    Or.inl rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro point hpoint
    have hne : point ≠ 0 := by simpa using hpoint.2
    have hout := (mem_invertedExterior_iff domain critical hcritical point hne).mp hpoint.1
    have hcomp := harmonic_comp_analytic green (inversion critical) point
      (hharmonic _ hout) (inversion_analytic critical point hne)
    apply (harmonicAt_congr_nhds (f₁ := inversionGreen critical green)
      (f₂ := green ∘ inversion critical) ?_).mpr hcomp
    filter_upwards [eventually_ne_nhds hne] with member hmember
    simp only [inversionGreen, if_neg hmember, Function.comp_apply]
  · intro point hpoint
    have hne : point ≠ 0 := by simpa using hpoint.2
    simp only [inversionGreen, if_neg hne]
    exact hpositive _ ((mem_invertedExterior_iff domain critical hcritical point hne).mp hpoint.1)
  · let chart : ℂ → ℂ := fun point => -point / critical
    have hchart_analytic : AnalyticAt ℂ chart 0 := analyticAt_id.neg.div_const
    have hchart_zero : chart 0 = 0 := by simp [chart]
    have hchart_ne (point : ℂ) (hne : point ≠ 0) : chart point ≠ 0 :=
      div_ne_zero (neg_ne_zero.mpr hne) hcritical
    have hchart_tendsto : Tendsto chart (𝓝[≠] (0 : ℂ)) (𝓝[≠] (0 : ℂ)) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨?_, ?_⟩
      · simpa only [hchart_zero] using hchart_analytic.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with point hpoint
        exact hchart_ne point hpoint
    refine ⟨fun point => regular (chart point) + Real.log ‖critical‖, ?_, ?_⟩
    · have hcomp := harmonic_comp_analytic regular chart 0
        (by simpa only [hchart_zero] using hregular_harmonic) hchart_analytic
      exact hcomp.add (harmonicAt_const _)
    · filter_upwards [hchart_tendsto.eventually hregular_eq, self_mem_nhdsWithin] with point hpoint hne
      have hpoint_ne : point ≠ 0 := by simpa using hne
      have hnorm : ‖point‖ ≠ 0 := norm_ne_zero_iff.mpr hne
      have hchart_inv : (chart point)⁻¹ = inversion critical point := by
        dsimp [chart, inversion]
        field_simp
      rw [hchart_inv] at hpoint
      simp only [chart, norm_div, norm_neg, Real.log_div hnorm hcriticalnorm] at hpoint
      simp only [inversionGreen, if_neg hpoint_ne, sub_zero]
      dsimp only [chart]
      linarith
  · intro point hpoint
    have hne : point ≠ 0 := by
      intro heq
      subst point
      exact hpoint.2 (mem_interior_iff_mem_nhds.mpr
        (invertedExterior_zero_nhds domain hbounded critical hcritical))
    have himage_frontier : inversion critical point ∈ frontier (closure domain) := by
      rw [hfrontier]
      exact invertedExterior_frontier_subset domain hbounded critical hcritical point hpoint
    have hmap : Tendsto (inversion critical) (𝓝[invertedExterior domain critical] point)
        (𝓝[(closure domain)ᶜ] (inversion critical point)) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨(inversion_analytic critical point hne).continuousAt.tendsto.mono_left
        nhdsWithin_le_nhds, ?_⟩
      filter_upwards [self_mem_nhdsWithin, eventually_ne_nhdsWithin hne] with member hmember hmember_ne
      exact (mem_invertedExterior_iff domain critical hcritical member hmember_ne).mp hmember
    apply ((hboundary _ himage_frontier).comp hmap).congr'
    filter_upwards [eventually_ne_nhdsWithin hne] with member hmember
    simp only [inversionGreen, if_neg hmember, Function.comp_apply]
  · intro point hpoint
    by_cases hne : point = 0
    · simp only [inversionGreen, if_pos hne]
    · simp only [inversionGreen, if_neg hne]
      apply houtside
      by_contra hout
      exact hpoint ((mem_invertedExterior_iff domain critical hcritical point hne).mpr hout)

theorem inversion_green_identity_proved
    (inverse : ℂ → ℂ) (hinverse : IsUnivalentOn inverse (disk 1)) (hzero : inverse 0 = 0)
    (height : ℝ) (hheight : height ∈ Ioo 0 1) (critical : ℂ) (hcritical : critical ≠ 0)
    (homit : critical ∉ inverse '' disk 1) (greenExterior greenImage : ℂ → ℝ)
    (hgreenExterior : IsClassicalExteriorGreen (closure (inverseDomain inverse height)) greenExterior)
    (hgreenImage : IsClassicalGreen (exteriorImage inverse height critical) 0 greenImage) :
    greenExterior critical = greenImage (-1) := by
  have hdomain := (inverse_jordan_domain_proved inverse hinverse hzero height hheight).1
  have hbase : (0 : ℂ) ∈ inverseDomain inverse height :=
    ⟨0, by simp [disk, hheight.1], hzero⟩
  have hpullback := invertedExterior_green (inverseDomain inverse height) hdomain.1
    hdomain.2.2.2.1 hbase (inverseDomain_regular inverse hinverse height hheight)
    critical hcritical greenExterior hgreenExterior
  obtain ⟨hgeometry, _, _⟩ := exterior_image_geometry_proved inverse hinverse hzero
    height hheight critical hcritical homit
  have heq := finite_green_unique (exteriorImage inverse height critical) hgeometry.1
    hgeometry.2.1 0 (inversionGreen critical greenExterior) greenImage hpullback hgreenImage
    (-1) (by norm_num)
  simpa only [inversionGreen, if_neg (by norm_num : (-1 : ℂ) ≠ 0), inversion,
    div_neg, div_one, neg_neg] using heq

end SmaleRate.Proofs

#check SmaleRate.Proofs.harmonic_comp_analytic
#print axioms SmaleRate.Proofs.harmonic_comp_analytic
#check SmaleRate.Proofs.invertedExterior_green
#print axioms SmaleRate.Proofs.invertedExterior_green
#check SmaleRate.Proofs.inversion_green_identity_proved
#print axioms SmaleRate.Proofs.inversion_green_identity_proved
