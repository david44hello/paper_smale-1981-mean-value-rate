/-
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
module

public import SmaleRate.Proofs.GreenBoundary

set_option backward.proofsInPublic true

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set Filter Metric InnerProductSpace
open scoped Topology

def conformalDiskGreen (equiv : OpenPartialHomeomorph ℂ ℂ) (point : ℂ) : ℝ := by
  classical
  exact if point ∈ equiv.source then -Real.log ‖equiv point‖ else 0

theorem green_from_disk_equivalence (equiv : OpenPartialHomeomorph ℂ ℂ)
    (hunit : equiv.target = disk 1) (hbounded : Bornology.IsBounded equiv.source)
    (pole : ℂ) (hpole : pole ∈ equiv.source) (hzero : equiv pole = 0)
    (hanalytic : AnalyticOnNhd ℂ (equiv : ℂ → ℂ) equiv.source)
    (hderivative : deriv (equiv : ℂ → ℂ) pole ≠ 0) :
    IsClassicalGreen equiv.source pole (conformalDiskGreen equiv) := by
  have hnonzero : ∀ point ∈ equiv.source, point ≠ pole → equiv point ≠ 0 := by
    intro point hpoint hne heq
    exact hne (equiv.injOn hpoint hpole (heq.trans hzero.symm))
  refine ⟨hbounded, hpole, ?_, ?_, ?_, ?_, ?_⟩
  · intro point hpoint
    have hne : point ≠ pole := by simpa using hpoint.2
    have hharmonic := ((hanalytic point hpoint.1).harmonicAt_log_norm
      (hnonzero point hpoint.1 hne)).neg
    apply (harmonicAt_congr_nhds (f₁ := conformalDiskGreen equiv)
      (f₂ := -(fun member : ℂ => Real.log ‖equiv member‖)) ?_).mpr hharmonic
    filter_upwards [equiv.open_source.mem_nhds hpoint.1] with member hmember
    simp [conformalDiskGreen, hmember]
  · intro point hpoint
    have hne : point ≠ pole := by simpa using hpoint.2
    have hmem := equiv.map_source hpoint.1
    rw [hunit] at hmem
    have hnorm : ‖equiv point‖ < 1 := mem_ball_zero_iff.mp hmem
    simp only [conformalDiskGreen, if_pos hpoint.1]
    exact neg_pos.mpr (Real.log_neg (norm_pos_iff.mpr (hnonzero point hpoint.1 hne)) hnorm)
  · have hslope : AnalyticAt ℂ (dslope (equiv : ℂ → ℂ) pole) pole := by
      obtain ⟨series, hseries⟩ := hanalytic pole hpole
      exact ⟨series.fslope, hseries.has_fpower_series_dslope_fslope⟩
    have hslope_ne : dslope (equiv : ℂ → ℂ) pole pole ≠ 0 := by
      rw [dslope_same]
      exact hderivative
    refine ⟨fun member : ℂ => -Real.log ‖dslope (equiv : ℂ → ℂ) pole member‖, ?_, ?_⟩
    · change HarmonicAt (-(fun member : ℂ => Real.log ‖dslope (equiv : ℂ → ℂ) pole member‖)) pole
      exact (hslope.harmonicAt_log_norm hslope_ne).neg
    · have hsource : ∀ᶠ member : ℂ in 𝓝[≠] pole, member ∈ equiv.source :=
        nhdsWithin_le_nhds (equiv.open_source.mem_nhds hpole)
      filter_upwards [hsource, self_mem_nhdsWithin] with member hmember hne
      have hdistinct : member ≠ pole := by simpa using hne
      have hequiv_ne := hnonzero member hmember hdistinct
      have hquotient : dslope (equiv : ℂ → ℂ) pole member = equiv member/(member-pole) := by
        rw [dslope_of_ne _ hdistinct, slope_def_field, hzero, sub_zero]
      simp only [conformalDiskGreen, if_pos hmember]
      rw [hquotient, norm_div,
        Real.log_div (norm_ne_zero_iff.mpr hequiv_ne) (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hdistinct))]
      ring
  · intro point hpoint
    have hnorm := disk_equivalence_norm_boundary equiv hunit point hpoint
    have hlimit : Tendsto (fun member : ℂ => -Real.log ‖equiv member‖)
        (𝓝[equiv.source] point) (𝓝 0) := by
      have hlog := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hnorm
      simpa only [Function.comp_def, Real.log_one, neg_zero] using hlog.neg
    apply hlimit.congr'
    filter_upwards [self_mem_nhdsWithin] with member hmember
    simp [conformalDiskGreen, hmember]
  · intro point hpoint
    simp [conformalDiskGreen, hpoint]

end SmaleRate.Proofs

#check SmaleRate.Proofs.green_from_disk_equivalence
#print axioms SmaleRate.Proofs.green_from_disk_equivalence
