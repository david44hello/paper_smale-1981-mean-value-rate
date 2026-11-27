/-
SmaleRate — geometry of a smaller disk under a univalent branch.
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
open Set Filter Metric Topology

theorem smaller_closed_disk_subset (height : ℝ) (hheight : height ∈ Ioo 0 1) :
    closedBall (0 : ℂ) height ⊆ disk 1 := by
  intro point hpoint
  exact (mem_ball_zero_iff.mpr ((mem_closedBall_zero_iff.mp hpoint).trans_lt hheight.2))

theorem inverse_image_closure (inverse : ℂ → ℂ) (hinverse : IsUnivalentOn inverse (disk 1))
    (height : ℝ) (hheight : height ∈ Ioo 0 1) :
    closure (inverseDomain inverse height) = inverse '' closedBall 0 height := by
  have hcont := hinverse.1.continuousOn.mono (smaller_closed_disk_subset height hheight)
  have hcompact := (isCompact_closedBall (0 : ℂ) height).image_of_continuousOn hcont
  apply le_antisymm
  · exact closure_minimal (image_mono ball_subset_closedBall) hcompact.isClosed
  · have hclosure : closure (ball (0 : ℂ) height) = closedBall 0 height :=
      closure_ball 0 hheight.1.ne'
    have hcont' : ContinuousOn inverse (closure (ball (0 : ℂ) height)) := hclosure.symm ▸ hcont
    simpa only [inverseDomain, disk, hclosure] using hcont'.image_closure

theorem inverse_image_open (inverse : ℂ → ℂ) (hinverse : IsUnivalentOn inverse (disk 1))
    (height : ℝ) (hheight : height ∈ Ioo 0 1) : IsOpen (inverseDomain inverse height) := by
  have hanalytic : AnalyticOnNhd ℂ inverse (disk 1) :=
    (Complex.analyticOnNhd_iff_differentiableOn isOpen_ball).mpr hinverse.1
  rcases hanalytic.is_constant_or_isOpen (convex_ball (0 : ℂ) 1).isPreconnected with
    ⟨value, hconstant⟩ | hopen
  · have hzero : (0 : ℂ) ∈ disk 1 := by simp [disk]
    have hhalf : (1/2 : ℂ) ∈ disk 1 := by norm_num [disk, mem_ball_zero_iff]
    have heq := hinverse.2 hzero hhalf ((hconstant 0 hzero).trans (hconstant (1/2) hhalf).symm)
    norm_num at heq
  · exact hopen (disk height) (ball_subset_ball hheight.2.le) isOpen_ball

theorem inverse_image_frontier (inverse : ℂ → ℂ) (hinverse : IsUnivalentOn inverse (disk 1))
    (height : ℝ) (hheight : height ∈ Ioo 0 1) :
    frontier (inverseDomain inverse height) = inverse '' sphere 0 height := by
  have hinj := hinverse.2.mono (smaller_closed_disk_subset height hheight)
  have hopen := inverse_image_open inverse hinverse height hheight
  rw [frontier, hopen.interior_eq, inverse_image_closure inverse hinverse height hheight]
  change inverse '' closedBall 0 height \ inverse '' ball 0 height = inverse '' sphere 0 height
  rw [← hinj.image_sdiff_subset ball_subset_closedBall, closedBall_sdiff_ball]

theorem inverse_image_closure_subset (inverse : ℂ → ℂ) (hinverse : IsUnivalentOn inverse (disk 1))
    (height : ℝ) (hheight : height ∈ Ioo 0 1) :
    closure (inverseDomain inverse height) ⊆ inverse '' disk 1 := by
  rw [inverse_image_closure inverse hinverse height hheight]
  exact image_mono (smaller_closed_disk_subset height hheight)

theorem scaled_unit_sphere (height : ℝ) (hheight : 0 < height) :
    (fun point : ℂ => (height : ℂ) * point) '' sphere 0 1 = sphere 0 height := by
  have hne : (height : ℂ) ≠ 0 := by exact_mod_cast hheight.ne'
  ext point
  constructor
  · rintro ⟨unit, hunit, rfl⟩
    rw [mem_sphere_zero_iff_norm] at hunit ⊢
    simp [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hheight, hunit]
  · intro hpoint
    refine ⟨point / (height : ℂ), ?_, ?_⟩
    · rw [mem_sphere_zero_iff_norm] at hpoint ⊢
      simp [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hheight, hpoint, hheight.ne']
    · exact mul_div_cancel₀ point hne

theorem inverse_jordan_domain_proved (inverse : ℂ → ℂ) (hinverse : IsUnivalentOn inverse (disk 1))
    (_hzero : inverse 0 = 0) (height : ℝ) (hheight : height ∈ Ioo 0 1) :
    IsBoundedJordanDomain (inverseDomain inverse height) ∧
    closure (inverseDomain inverse height) = inverse '' closedBall 0 height ∧
    closure (inverseDomain inverse height) ⊆ inverse '' disk 1 := by
  have hsubset : disk height ⊆ disk 1 := ball_subset_ball hheight.2.le
  have hcontinuous := hinverse.1.continuousOn.mono hsubset
  have hclosedcont := hinverse.1.continuousOn.mono (smaller_closed_disk_subset height hheight)
  have hcompact := (isCompact_closedBall (0 : ℂ) height).image_of_continuousOn hclosedcont
  have hmaps : MapsTo (fun point : ℂ => (height : ℂ) * point) (sphere 0 1) (disk 1) := by
    intro point hpoint
    have hsphere : (height : ℂ) * point ∈ sphere (0 : ℂ) height :=
      (scaled_unit_sphere height hheight.1) ▸ ⟨point, hpoint, rfl⟩
    exact smaller_closed_disk_subset height hheight (sphere_subset_closedBall hsphere)
  refine ⟨⟨inverse_image_open inverse hinverse height hheight,
    (convex_ball (0 : ℂ) height).isPreconnected.image inverse hcontinuous,
    ⟨inverse 0, 0, by simp [disk, hheight.1], rfl⟩,
    hcompact.isBounded.subset (image_mono ball_subset_closedBall), ?_⟩,
    inverse_image_closure inverse hinverse height hheight,
    inverse_image_closure_subset inverse hinverse height hheight⟩
  refine ⟨fun point : ℂ => inverse ((height : ℂ) * point),
    hinverse.1.continuousOn.comp (continuous_const.mul continuous_id).continuousOn hmaps, ?_, ?_⟩
  · intro first hfirst second hsecond heq
    have hne : (height : ℂ) ≠ 0 := by exact_mod_cast hheight.1.ne'
    exact mul_left_cancel₀ hne (hinverse.2 (hmaps hfirst) (hmaps hsecond) heq)
  · rw [← image_image, scaled_unit_sphere height hheight.1]
    exact (inverse_image_frontier inverse hinverse height hheight).symm

end SmaleRate.Proofs
