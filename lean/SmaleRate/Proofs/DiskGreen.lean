/-
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
module

public import SmaleRate.Defs.AnalyticBackground

set_option backward.proofsInPublic true

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set Filter Metric InnerProductSpace
open scoped Topology

theorem diskGreen_eq_neg_log (point : ℂ) (hpoint : point ∈ disk 1) :
    diskGreen point = -Real.log ‖point‖ := by
  simp [diskGreen, hpoint, one_div]

theorem disk_green_instance_proved : IsClassicalGreen (disk 1) 0 diskGreen := by
  have hbase : (0 : ℂ) ∈ disk 1 := by simp [disk]
  refine ⟨isBounded_ball, hbase, ?_, ?_, ?_, ?_, ?_⟩
  · intro point hpoint
    have hne : point ≠ 0 := by simpa using hpoint.2
    have hharmonic : HarmonicAt (fun member : ℂ => -Real.log ‖member‖) point := by
      change HarmonicAt (-(fun member : ℂ => Real.log ‖member‖)) point
      exact ((analyticAt_id : AnalyticAt ℂ (fun member : ℂ => member) point).harmonicAt_log_norm hne).neg
    apply (harmonicAt_congr_nhds (f₁ := diskGreen) (f₂ := fun member : ℂ => -Real.log ‖member‖) ?_).mpr hharmonic
    filter_upwards [isOpen_ball.mem_nhds hpoint.1] with member hmember
    exact diskGreen_eq_neg_log member hmember
  · intro point hpoint
    have hne : point ≠ 0 := by simpa using hpoint.2
    rw [diskGreen_eq_neg_log point hpoint.1]
    have hnorm : ‖point‖ < 1 := mem_ball_zero_iff.mp hpoint.1
    exact neg_pos.mpr (Real.log_neg (norm_pos_iff.mpr hne) hnorm)
  · refine ⟨fun _ : ℂ => (0 : ℝ), harmonicAt_const 0, ?_⟩
    have hball : ∀ᶠ point : ℂ in 𝓝[≠] 0, point ∈ disk 1 :=
      nhdsWithin_le_nhds (isOpen_ball.mem_nhds hbase)
    filter_upwards [hball] with point hpoint
    rw [diskGreen_eq_neg_log point hpoint]
    simp
  · intro point hpoint
    have hsphere : point ∈ sphere (0 : ℂ) 1 := by
      simpa only [disk, frontier_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)] using hpoint
    have hnorm : ‖point‖ = 1 := mem_sphere_zero_iff_norm.mp hsphere
    have hnormne : ‖point‖ ≠ 0 := by rw [hnorm]; norm_num
    have hcontinuous : ContinuousAt (fun member : ℂ => -Real.log ‖member‖) point :=
      (continuous_norm.continuousAt.log hnormne).neg
    have hlimit : Tendsto (fun member : ℂ => -Real.log ‖member‖)
        (𝓝[disk 1] point) (𝓝 0) := by
      simpa only [hnorm, Real.log_one, neg_zero] using
        hcontinuous.tendsto.mono_left nhdsWithin_le_nhds
    apply hlimit.congr'
    filter_upwards [self_mem_nhdsWithin] with member hmember
    exact (diskGreen_eq_neg_log member hmember).symm
  · intro point hpoint
    simp [diskGreen, hpoint]

end SmaleRate.Proofs

#check SmaleRate.Proofs.disk_green_instance_proved
#print axioms SmaleRate.Proofs.disk_green_instance_proved
